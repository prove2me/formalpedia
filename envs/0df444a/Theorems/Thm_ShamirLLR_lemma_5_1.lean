-- Prove2me | Theorems.Thm_ShamirLLR_lemma_5_1
-- name    : ShamirLLR.lemma_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T08:27:25.559429+00:00
-- url     : https://prove2.me/theorems/e643ad40-7f5d-46dd-98ae-b8cb8485e445
-- title:
--   Lemma 5.1 — product refinement
-- statement:
--   Fix the finite collection $\mathcal N$ (dimensions at most $D$) and $K=D+2$. There is a constant $C$, depending only on this local data and not on $p$, $m$, $r$ or the forms, such that the following holds. Let $p$ be an odd prime, $r\ge1$, $L_1,\dots,L_m:\mathbb F_p^r\to\mathbb F_p$ arbitrary linear forms, $(G^{(i)}/\Gamma^{(i)})\in\mathcal N$, $\Phi_i:G^{(i)}/\Gamma^{(i)}\to\mathbb C$ with vertical frequency $\nu_i$ and $\|\Phi_i\|_{C^K(X^{(i)})}\le1$, $g^{(i)}\in\mathrm{poly}(\mathbb Z,G^{(i)}_\bullet)$ $p$-periodic modulo $\Gamma^{(i)}$, and $0<\delta\le1/10$. If
--   $$
--   \Bigl|\mathbb E_{x\in\mathbb F_p^r}\prod_{i=1}^m\Phi_i\bigl(g^{(i)}(L_i(x))\Gamma^{(i)}\bigr)\Bigr|\ge\delta
--   \quad\text{and}\quad
--   \log p\ge C\bigl(m^2\log(2m)+m\log(1/\delta)\bigr),
--   $$
--   then there are product first-level characters $\xi_1,\dots,\xi_t$, $0\le t\le Dm$, each constant modulo $1$ on the orbit $(g^{(i)}(L_i(x))\Gamma^{(i)})_i$, $x\in\mathbb F_p^r$, each of complexity at most
--   $$
--   B=\exp\bigl(C(m\log(2m)+\log(1/\delta))\bigr),
--   $$
--   whose common real kernel $K_0=\bigcap_j\ker d\xi_j\subseteq\bigoplus_i\mathrm{Lie}(G^{(i)})$ satisfies $\sum_i d\nu_i([v_i,w_i])=0$ for all $v,w\in K_0$.
--
--   This turns a large product average of nilsequences into short character equations with an isotropic common kernel.
--
--   Differences from the source:
--   - encoding: product first-level characters, their complexity and constancy modulo 1 → families of first-level integer rows $(k_i)_i$ with value $\sum_ik_i\cdot\psi^{(i)}(g_i)$, complexity $\sum_i\|k_i\|_1$, and integer differences between the values at any two orbit points, the sequences evaluated at representatives $z.\mathrm{val}$; reason: the definitions of §3.4; periodicity makes the values modulo 1 independent of the representatives (p.33)
--   - encoding: $\bigoplus_i\mathrm{Lie}(G^{(i)})$, $d\xi$, $d\nu_i([v_i,w_i])$ → $\bigoplus_i\mathbb R^{d_i}$ in basis coordinates, $d\xi(v)=\sum k_{i,j}v_{i,j}$, $d\nu_i([v_i,w_i])=k_{\nu_i}\cdot[v_i,w_i]$ via the structure constants; reason: Eq. (20), pp.22–23
--   - encoding: the setting of Sections 4–5 ($\mathcal N$ fixed, $p$ odd, $m$ shares) → hypotheses: $\mathcal N$ a finite nonempty set of `LSS.Nilmanifold 2`, $D\ge1$ bounding dimensions, $p$ prime $\neq2$, $m\ge1$; reason: §4.1 data; $m\ge1$ only excludes the undefined $\log(2\cdot0)$
-- source:
--   Hwang–Maji–Shkredov–Ye, Local Leakage Resilience of Multiplication-friendly Shamir Secret Sharing (manuscript, 2 Nov 2026; held version, sha256 fcd6871f…), Lemma 5.1, Eq. (25)–(28), pp.32–33 (PDF pp.33–34)

import Mathlib
import Definitions.Def_LSSNil
import Definitions.Def_ShamirLLR_nilCoords
import Definitions.Def_ShamirLLR_nilSmooth

set_option autoImplicit false

namespace ShamirLLR

/-- **Lemma 5.1 (Product refinement).** Fix the finite collection `N` (dimensions at most `D`) and
`K = D + 2`. There is a constant `C`, depending only on the fixed local data and independent of
`r` and the forms, such that: let `r ≥ 1`, `L₁, …, L_m : 𝔽_p^r → 𝔽_p` arbitrary linear forms,
`(G^{(i)}/Γ^{(i)}) ∈ N`, `Φ_i : G^{(i)}/Γ^{(i)} → ℂ` with vertical frequency `ν_i` and
`‖Φ_i‖_{C^K(X^{(i)})} ≤ 1`, `g^{(i)} ∈ poly(ℤ, G^{(i)}_•)` `p`-periodic modulo `Γ^{(i)}`, and
`0 < δ ≤ 1/10`. If `|𝔼_{x ∈ 𝔽_p^r} ∏_i Φ_i(g^{(i)}(L_i(x))Γ^{(i)})| ≥ δ` (25) and
`log p ≥ C(m² log(2m) + m log(1/δ))` (26), then there are product first-level characters
`ξ₁, …, ξ_t`, `0 ≤ t ≤ Dm`, each constant modulo `1` on the orbit
`(g^{(i)}(L_i(x))Γ^{(i)})_{i}`, `x ∈ 𝔽_p^r`, each of complexity at most
`B = exp(C(m log(2m) + log(1/δ)))` (27), whose common real kernel
`K₀ = ⋂_j ker dξ_j ⊆ ⊕_i Lie(G^{(i)})` satisfies `∑_i dν_i([v_i, w_i]) = 0` for all
`v, w ∈ K₀` (28).

Source: Hwang–Maji–Shkredov–Ye, manuscript of 2 Nov 2026 (held version, sha256 fcd6871f…),
Lemma 5.1, Eq. (25)–(28), pp.32–33; product characters and differentials, §3.4, pp.21–23.

**Formalization Note.** `N` is a finite nonempty set of `LSS.Nilmanifold 2`; `p` is an odd prime
and `m ≥ 1`. A product first-level character is a family of first-level integer rows
`(k_i)_i`, its complexity `∑_i ‖k_i‖₁`, its value `∑_i k_i · ψ₁^{(i)}(g_i)`. Group-valued
sequences are evaluated at the representatives `z.val`; constancy modulo `1` is that the
difference of the values at any two points of the orbit is an integer. `dξ(v) = ∑ k_{i,j} v_{i,j}`
and `dν_i([v_i, w_i]) = k_{ν_i} · [v_i, w_i]` in basis coordinates. -/
theorem lemma_5_1 (N : Set (LSS.Nilmanifold 2)) (hNfin : N.Finite) (hNne : N.Nonempty)
    (D : ℕ) (hD : 1 ≤ D) (hND : ∀ G ∈ N, G.d ≤ D) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (m r : ℕ), 1 ≤ m → 1 ≤ r →
      ∀ (L : Fin m → (Fin r → ZMod p) →ₗ[ZMod p] ZMod p) (Gs : Fin m → LSS.Nilmanifold 2),
      (∀ i, Gs i ∈ N) →
      ∀ (Φ : (i : Fin m) → (Gs i).Mat → ℂ) (kν : (i : Fin m) → Fin (Gs i).d → ℤ),
      (∀ i, IsCR (Gs i) (D + 2) (Φ i) ∧ CRNormLE (Gs i) (D + 2) 1 (Φ i) ∧
        HasVerticalFreq (Gs i) (Φ i) (kν i)) →
      ∀ g : (i : Fin m) → ℤ → (Gs i).Mat, (∀ i, IsQuadPoly (Gs i) (g i) ∧ IsPPeriodic (Gs i) p (g i)) →
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 10 →
      δ ≤ ‖((p : ℂ) ^ r)⁻¹ * ∑ x : Fin r → ZMod p, ∏ i, Φ i (g i ((L i x).val : ℤ))‖ →
      C * ((m : ℝ) ^ 2 * Real.log (2 * m) + m * Real.log (1 / δ)) ≤ Real.log p →
      ∃ t : ℕ, t ≤ D * m ∧ ∃ ξ : Fin t → (i : Fin m) → Fin (Gs i).d → ℤ,
        (∀ l, (∀ i, IsFirstLevel (Gs i) (ξ l i)) ∧
          (∀ x x' : Fin r → ZMod p, ∃ n : ℤ,
            ∑ i, charVal (Gs i) (ξ l i) (g i ((L i x).val : ℤ)) -
              ∑ i, charVal (Gs i) (ξ l i) (g i ((L i x').val : ℤ)) = n) ∧
          ((∑ i, ∑ j, |ξ l i j| : ℤ) : ℝ) ≤
            Real.exp (C * (m * Real.log (2 * m) + Real.log (1 / δ)))) ∧
        ∀ v w : (i : Fin m) → Fin (Gs i).d → ℝ,
          (∀ l, ∑ i, ∑ j, (ξ l i j : ℝ) * v i j = 0) →
          (∀ l, ∑ i, ∑ j, (ξ l i j : ℝ) * w i j = 0) →
          ∑ i, ∑ j, (kν i j : ℝ) * lieBr (Gs i) (v i) (w i) j = 0 := by sorry

end ShamirLLR
