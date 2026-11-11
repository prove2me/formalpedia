-- Prove2me | Theorems.Thm_ShamirLLR_lemma_7_3
-- name    : ShamirLLR.lemma_7_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T08:28:36.778206+00:00
-- url     : https://prove2.me/theorems/56b044c7-1743-4f45-8d0a-39c481fd1057
-- title:
--   Lemma 7.3 — local reduction to a quadratic torus
-- statement:
--   Let $D\ge1$ and let $G/\Gamma$ be a degree-two filtered nilmanifold of dimension at most $D$. There is $C_G\ge1$, depending only on $G$ and $D$, such that: let $H_0\ge2$, $p$ a prime with $p>D!\,H_0^D$, $\xi_j=k_j\cdot\psi_1$ finitely many first-level characters with $\|k_j\|_\infty\le H_0$, and $g:\mathbb Z\to G$ a degree-two polynomial sequence, $p$-periodic modulo $\Gamma$, along which every $\xi_j(g(z))$ is constant modulo $1$. Put $H=\exp(\bigcap_j\ker d\xi_j)$, $\Gamma_H=H\cap\Gamma$, $Z=[H,H]$. Then
--
--   1. there are $c$ in the centered Mal'cev fundamental box ($\psi(c)\in(-1/2,1/2]^{d_G}$) and a degree-two polynomial sequence $h:\mathbb Z\to H$ for the inherited filtration with $g(z)\Gamma=c\,h(z)\Gamma$, $h(0)=\mathrm{id}_G$, and $h(z)^{-1}h(z+p)\in\Gamma_H$;
--   2. $H$ and $Z$ are connected and rational, and $Z$ is central in $G$;
--   3. with $d_H=\dim H-\dim Z\le D$, there are a continuous surjective homomorphism $\varphi:H\to\mathbb T^{d_H}$ with kernel $Z\Gamma_H$, and $\vartheta\in\mathbb T^{d_H}$, $\beta_1,\beta_2\in\mathbb F_p^{d_H}$ with
--   $$
--   \varphi(h(z))=\vartheta+\frac{\beta_1z+\beta_2z^2}{p}\pmod{\mathbb Z^{d_H}}\qquad(z\in\mathbb Z),
--   $$
--   and every Lipschitz $F:G/\Gamma\to[0,1]$ invariant under $Z$ satisfies $F(cx\Gamma)=A(\varphi(x))$ ($x\in H$) for some $A:\mathbb T^{d_H}\to[0,1]$ with $\|A\|_{\mathrm{Lip}}\le H_0^{C_G}\|F\|_{\mathrm{Lip}}$.
--
--   This reduces a commutator-invariant readout along a constrained orbit to a probability map on a quadratic torus orbit.
--
--   Differences from the source:
--   - generalization: "one of the local degree-two filtered nilmanifolds $G/\Gamma$ in the class $\mathcal G$, of dimension at most $D$", with $C_{\mathcal G}$ depending on the fixed geometric data of the class → every `LSS.Nilmanifold 2` $G$ with $d_G\le D$, with $C_G$ depending only on $G$ and $D$; reason: specializes to each member of the fixed finite collection $\mathcal N$, and the maximum of the finitely many $C_G$ is a class constant
--   - reading: "$c$ in the fixed Mal'cev fundamental box" → $\psi(c)\in(-1/2,1/2]^{d_G}$; reason: Step 1 of the proof uses the centered decomposition of §3.3
--   - reading: "$h\mapsto F(ch\Gamma)$ descends to $H/(Z\Gamma_H)\simeq\mathbb T^{d_H}$ … in suitable group coordinates on the torus" → a continuous surjective homomorphism $\varphi:H\to\mathbb T^{d_H}$ with kernel $Z\Gamma_H$, chosen with $c, h, \vartheta, \beta_1, \beta_2$ before $F$; the torus carries its product (sup) metric; reason: an isomorphism $H/(Z\Gamma_H)\simeq\mathbb T^{d_H}$ is such a $\varphi$; the coordinates are fixed before the readout
--   - encoding: connected, rational, $\dim$ → connectedness as subsets of matrix space, rationality by the coordinate criterion of §3.6 (a rational basis of the Lie algebra), dimensions as `finrank` of the Lie algebras in basis coordinates; reason: §3.6 states the coordinate criterion
--   - encoding: $\|A\|_{\mathrm{Lip}}\le H_0^{C_G}\|F\|_{\mathrm{Lip}}$ for Lipschitz $F$ → for every $K$ with $\|F\|_{\mathrm{Lip}}\le K$, $\|A\|_{\mathrm{Lip}}\le H_0^{C_G}K$; reason: equivalent formulation without real suprema
-- source:
--   Hwang–Maji–Shkredov–Ye, Local Leakage Resilience of Multiplication-friendly Shamir Secret Sharing (manuscript, 2 Nov 2026; held version, sha256 fcd6871f…), Lemma 7.3, p.50, and proof, pp.51–53 (PDF pp.51–54); centered box §3.3, p.20; rationality §3.6, p.25

import Mathlib
import Definitions.Def_LSSNil
import Definitions.Def_ShamirLLR_nilCoords
import Definitions.Def_ShamirLLR_nilSmooth
import Definitions.Def_ShamirLLR_charSubgroup
import Definitions.Def_ShamirLLR_torus

set_option autoImplicit false

namespace ShamirLLR

/-- **Lemma 7.3 (Local Reduction to a Quadratic Torus).** Let `D ≥ 1` and let `G/Γ` be a
degree-two filtered nilmanifold of dimension at most `D`. There is `C_G ≥ 1`, depending only on
`G` and `D`, such that the following holds. Let `H₀ ≥ 2`, `p` a prime with `p > D! H₀^D`, and
`ξ_j = k_j · ψ₁` finitely many first-level characters with `‖k_j‖_∞ ≤ H₀`. Let `g : ℤ → G` be a
degree-two polynomial sequence, `p`-periodic modulo `Γ`, with every `ξ_j(g(z))` constant modulo
`1`. Put `H = exp(⋂_j ker dξ_j)`, `Γ_H = H ∩ Γ`, `Z = [H, H]`. Then:
1. there are `c` in the fixed (centered) Mal'cev fundamental box and a degree-two polynomial
   sequence `h : ℤ → H` for the inherited filtration with `g(z)Γ = c h(z)Γ`, `h(0) = id_G`, and
   `h(z)Γ_H` `p`-periodic;
2. `H` and `Z` are connected and rational, and `Z` is central in `G`;
3. with `d_H = dim H − dim Z ≤ D`, `H/(ZΓ_H) ≃ 𝕋^{d_H}` through a continuous surjective
   homomorphism `φ : H → 𝕋^{d_H}` with kernel `ZΓ_H`; the orbit is
   `φ(h(z)) = ϑ + (β₁z + β₂z²)/p mod ℤ^{d_H}` with `ϑ ∈ 𝕋^{d_H}`, `β₁, β₂ ∈ 𝔽_p^{d_H}`; and every
   Lipschitz `F : G/Γ → [0, 1]` invariant under `Z` descends, `F(c x Γ) = A(φ(x))` for `x ∈ H`,
   to `A : 𝕋^{d_H} → [0, 1]` with `‖A‖_{Lip} ≤ H₀^{C_G} ‖F‖_{Lip}`.

Source: Hwang–Maji–Shkredov–Ye, manuscript of 2 Nov 2026 (held version, sha256 fcd6871f…),
Lemma 7.3, p.50, and its proof, pp.51–53 (centered box: §3.3, p.20; rationality: §3.6, p.25).

**Formalization Note.** The nilmanifold is `LSS.Nilmanifold 2`; first-level rows are integer rows
on all coordinates vanishing on the central ones; constancy modulo `1` is that differences of
values along the orbit are integers. `H`, `Lie(H)`, `[𝔥, 𝔥]` and `Z = exp([𝔥, 𝔥])` are
`charSubgroup`, `charLie`, `brSpan`, `commSubgroup`; dimensions are `finrank` of the Lie algebras;
rationality is the coordinate criterion of §3.6. `c, h, φ, ϑ, β₁, β₂` are chosen before `F`, and
the torus carries its product (sup) metric. `‖·‖_{Lip}` bounds are `LipNormLE`/`TorusLipNormLE`. -/
theorem lemma_7_3 (D : ℕ) (hD : 1 ≤ D) (G : LSS.Nilmanifold 2) (hGD : G.d ≤ D) :
    ∃ CG : ℝ, 1 ≤ CG ∧ ∀ H₀ : ℝ, 2 ≤ H₀ → ∀ (p : ℕ) [Fact p.Prime],
      (D.factorial : ℝ) * H₀ ^ D < p →
      ∀ (J : ℕ) (k : Fin J → Fin G.d → ℤ), (∀ j, IsFirstLevel G (k j)) →
        (∀ j l, (|k j l| : ℝ) ≤ H₀) →
      ∀ g : ℤ → G.Mat, IsQuadPoly G g → IsPPeriodic G p g →
        (∀ j (z z' : ℤ), ∃ n : ℤ, charVal G (k j) (g z) - charVal G (k j) (g z') = n) →
      ∃ c : G.Mat, G.Mem c ∧ (∀ l, -(1 / 2 : ℝ) < coord G c l ∧ coord G c l ≤ 1 / 2) ∧
      ∃ h : ℤ → G.Mat,
        (∃ h₀ h₁ h₂ : G.Mat, h₀ ∈ charSubgroup G k ∧ h₁ ∈ charSubgroup G k ∧
          h₂ ∈ charSubgroup G k ∧ G.MemFil 2 h₂ ∧ h = quadOrbit G h₀ h₁ h₂) ∧
        (∀ z : ℤ, ∃ γ : G.Mat, G.MemΓ γ ∧ g z = c * h z * γ) ∧ h 0 = 1 ∧
        (∀ z : ℤ, (h z)⁻¹ * h (z + p) ∈ charSubgroup G k ∧ G.MemΓ ((h z)⁻¹ * h (z + p))) ∧
        IsConnected (charSubgroup G k) ∧ IsConnected (commSubgroup G k) ∧
        IsRationalLie G (charLie G k) ∧ IsRationalLie G (brSpan G k) ∧
        (∀ z ∈ commSubgroup G k, ∀ x : G.Mat, G.Mem x → z * x = x * z) ∧
        Module.finrank ℝ (charLie G k) - Module.finrank ℝ (brSpan G k) ≤ D ∧
        ∃ φ : G.Mat → Torus (Module.finrank ℝ (charLie G k) - Module.finrank ℝ (brSpan G k)),
          ContinuousOn φ (charSubgroup G k) ∧
          (∀ θ, ∃ x ∈ charSubgroup G k, φ x = θ) ∧
          (∀ x ∈ charSubgroup G k, ∀ y ∈ charSubgroup G k, φ (x * y) = φ x + φ y) ∧
          (∀ x ∈ charSubgroup G k, φ x = 0 ↔
            ∃ z ∈ commSubgroup G k, ∃ γ ∈ charSubgroup G k, G.MemΓ γ ∧ x = z * γ) ∧
          ∃ (ϑ : Torus (Module.finrank ℝ (charLie G k) - Module.finrank ℝ (brSpan G k)))
            (β₁ β₂ : Fin (Module.finrank ℝ (charLie G k) - Module.finrank ℝ (brSpan G k)) →
              ZMod p),
            (∀ z : ℤ, φ (h z) = ϑ + fun l =>
              (((((β₁ l).val : ℝ) * z + ((β₂ l).val : ℝ) * z ^ 2) / p : ℝ) : UnitAddCircle)) ∧
            ∀ F : G.Mat → ℝ, (∀ x : G.Mat, G.Mem x → 0 ≤ F x ∧ F x ≤ 1) →
              (∀ z ∈ commSubgroup G k, ∀ x : G.Mat, G.Mem x → F (z * x) = F x) →
              ∀ K : ℝ, LipNormLE G F K →
              ∃ A : Torus (Module.finrank ℝ (charLie G k) - Module.finrank ℝ (brSpan G k)) → ℝ,
                (∀ t, 0 ≤ A t ∧ A t ≤ 1) ∧ (∀ x ∈ charSubgroup G k, F (c * x) = A (φ x)) ∧
                TorusLipNormLE A (H₀ ^ CG * K) := by sorry

end ShamirLLR
