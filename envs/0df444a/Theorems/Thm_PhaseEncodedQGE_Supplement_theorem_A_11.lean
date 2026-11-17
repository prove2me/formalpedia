-- Prove2me | Theorems.Thm_PhaseEncodedQGE_Supplement_theorem_A_11
-- name    : PhaseEncodedQGE.Supplement.theorem_A_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T10:31:27.706543+00:00
-- url     : https://prove2.me/theorems/09f4f9d5-a851-4122-a8c8-03c0ef4728ec
-- title:
--   Theorem A.11 (= 4.1) — two-defect class values $p_1=\mu_2 f(a,k)$ and the seven-class injectivity criterion
-- statement:
--   Let $G$ be a cubic graph on $n$ vertices under a degree-prepared member (PE-X1, PE-Y1 or PE-X2) with mixer profile $h$, and write $c=\cos(\eta/2)$, $s=\sin(\eta/2)$, $t=s/c$. For a two-defect outcome $x$ with defect set $D=\{u,v\}$, its class is $(a,k)$ with $a=\mathbf 1[uv\in E]$ and $k=|N(u)\cap N(v)|$.
--
--   1. Every two-defect outcome of class $(a,k)$ has $p_1(x)=\mu_2 f(a,k)$, $\mu_2=c^4s^{2(n-2)}$, with
--   $$f(a,k)=\frac{(n-8+2a+k)h(0)+(6-2a-2k)h(1)+k\,h(2)}{t}-2t\,h(a).$$
--   2. $f$ is affine in the class labels: $f(a,k)=f(0,0)+k\Delta_k+a\Delta_a$ with $\Delta_k=[h(0)-2h(1)+h(2)]/t$ and $\Delta_a=2(h(0)-h(1))(t+1/t)$.
--   3. $f$ takes seven distinct values on the seven classes iff $\Delta_k\ne0$ and $\Delta_a/\Delta_k\notin\{-2,-1,0,1,2,3\}$.
--   4. Explicitly, with $A=n-8+2a+k$, $B=2(1-a)$, $h_e=\cos3\gamma+\cos6\gamma$, $h_o=\cos\gamma+\cos2\gamma$:
--   $$f_{X1}=\frac{A\cos3\gamma+(n-2-A)\cos\gamma}{t}-t\big[B\cos3\gamma+(2-B)\cos\gamma\big],$$
--   $$f_{Y1}=\frac{(3k+2a-6)\sin\gamma-A\sin3\gamma}{t}+2t\big[a\sin\gamma+(1-a)\sin3\gamma\big],$$
--   $$f_{X2}=\frac{A\,h_e+(n-2-A)h_o}{t}-t\big[B\,h_e+(2-B)h_o\big].$$
--   5. The increments are: PE-X1, $\Delta_k=(\cos3\gamma-\cos\gamma)/t=-4\cos\gamma\sin^2\gamma/t$, $\Delta_a/\Delta_k=2(1+t^2)$; PE-Y1, $\Delta_k=(3\sin\gamma-\sin3\gamma)/t=4\sin^3\gamma/t$, $\Delta_a/\Delta_k=-(1+t^2)\cos2\gamma/\sin^2\gamma$; PE-X2, $\Delta_k=(h_e-h_o)/t$, $\Delta_a/\Delta_k=2(1+t^2)$.
--   6. Hence PE-X1 is injective iff $\gamma\notin\frac\pi2\mathbb Z$ and $t^2\ne\frac12$; PE-X2 iff $h_e\ne h_o$ and $t^2\ne\frac12$; PE-Y1 iff $\sin\gamma\ne0$ and $(1+t^2)\cos2\gamma/\sin^2\gamma\notin\{-3,\dots,2\}$.
--
--   This is the bridge from the two-defect block of the sorted readout to the pair census: under the injectivity condition the seven classes have distinct first-order values, so the block determines $(N_{a,k})$ and with it $C_3$, $C_4$ and $D_\diamond$.
--
--   **Formalization Note** The affine identity and the explicit forms are stated on the seven classes. The member conditions say that the class-value function of the member's profile is injective on the seven classes.
--
--   Differences from the source:
--   - encoding: $t$ and $1/t$ used without comment → hypotheses $\cos(\eta/2)\ne0$ and $\sin(\eta/2)\ne0$; reason: they exclude only the angles at which t or 1/t is undefined (Lean's x/0 = 0 would otherwise give junk values)
--   - encoding: the ratios $\Delta_a/\Delta_k$ of (34)–(36) → $\Delta_k\ne0\Rightarrow\Delta_a/\Delta_k=\rho$; reason: a ratio is defined only where its denominator is nonzero; Lean's x/0 = 0 would make the unconditional equation false at Δ_k = 0, where the paper's ratio is undefined
-- source:
--   Miller, Lee, Structural Accessibility in Phase-Encoded Quantum Graph Embeddings, STOC 2027 submission (build 2026-11-03, sha256 f1132658…7c51), App. A.1.3, p.16 (PDF p.17), Theorem A.11, eqs. (28)–(36) (= Theorem 4.1, p.8 (PDF p.9), eqs. (12)–(13))

import Mathlib
import Definitions.Def_PhaseEncodedQGE_Circuit
import Definitions.Def_PhaseEncodedQGE_Profile
import Definitions.Def_PhaseEncodedQGE_Supplement_GraphCounts
import Definitions.Def_PhaseEncodedQGE_Supplement_ClassValue
set_option autoImplicit false

namespace PhaseEncodedQGE.Supplement

/-- Theorem A.11 (= Theorem 4.1), two-defect first-order class values (Miller, Lee, *Structural
Accessibility in Phase-Encoded Quantum Graph Embeddings*, STOC 2027 submission (build 2026-11-03),
App. A.1.3, p.16, eqs. (28)–(36); body twin Theorem 4.1, p.8, eqs. (12)–(13)).

For a degree-prepared member with profile `h`, every two-defect outcome of class `(a, k)` has
`p₁(x) = µ₂ f(a, k)`, `µ₂ = c⁴ s^{2(n−2)}`, with `f` as in (28). `f` is affine in the class labels,
`f(a, k) = f(0, 0) + k∆_k + a∆_a` with `∆_k`, `∆_a` as in (29)–(30), and takes seven distinct values
on the seven classes iff `∆_k ≠ 0` and `∆_a/∆_k ∉ {−2, …, 3}`. Explicitly (31)–(33) with
`A = n − 8 + 2a + k`, `B = 2(1 − a)`, `h_e = cos 3γ + cos 6γ`, `h_o = cos γ + cos 2γ`, with the
increments (34)–(36). Hence PE-X1 is injective iff `γ ∉ (π/2)ℤ` and `t² ≠ 1/2`; PE-X2 iff
`h_e ≠ h_o` and `t² ≠ 1/2`; PE-Y1 iff `sin γ ≠ 0` and `(1 + t²) cos 2γ / sin² γ ∉ {−3, …, 2}`.

**Formalization Note** Cubic graphs on `Fin n`, degree-aware preparation, `c = cos(η/2)`,
`s = sin(η/2)`, `t = tan(η/2) = s/c`; the hypotheses `c ≠ 0 ≠ s` exclude only the angles at which
`t` or `1/t` is undefined. A two-defect outcome of class `(a, k)` is an `x` with `D(x) = {u, v}`,
`u ≠ v`, `a = 1[uv ∈ E]`, `k = |N(u) ∩ N(v)|`. The members are `IsDegMember γ P r h`. The affine
identity and the explicit forms are stated on the seven classes (`IsPairClass`). Each ratio
`∆_a/∆_k = ρ` of (34)–(36) is stated where it is defined, as `∆_k ≠ 0 → ∆_a/∆_k = ρ`.
"`∉ {−2, …, 3}`" is `∀ z : ℤ, −2 ≤ z → z ≤ 3 → ∆_a/∆_k ≠ z`. -/
theorem theorem_A_11 :
    ∀ (n : ℕ) (η γ : ℝ), Real.cos (η / 2) ≠ 0 → Real.sin (η / 2) ≠ 0 →
      (∀ (P : Axis) (r : ℕ) (h : ℕ → ℝ), IsDegMember γ P r h →
        (∀ G : SimpleGraph (Fin n), IsCubic G → ∀ (x : Outcome n) (u v : Fin n), u ≠ v →
          defects x = {u, v} →
          bornDeriv (degPrep G η) P r G γ x =
            Real.cos (η / 2) ^ 4 * Real.sin (η / 2) ^ (2 * (n - 2)) *
              classValue h (Real.tan (η / 2)) n (adjBit G u v) (codegree G u v)) ∧
        (∀ a k : ℕ, IsPairClass a k →
          classValue h (Real.tan (η / 2)) n a k =
            classValue h (Real.tan (η / 2)) n 0 0 + (k : ℝ) * incrK h (Real.tan (η / 2)) +
              (a : ℝ) * incrA h (Real.tan (η / 2))) ∧
        (ClassInjective (classValue h (Real.tan (η / 2)) n) ↔
          (incrK h (Real.tan (η / 2)) ≠ 0 ∧
            ∀ z : ℤ, -2 ≤ z → z ≤ 3 →
              incrA h (Real.tan (η / 2)) / incrK h (Real.tan (η / 2)) ≠ (z : ℝ)))) ∧
      (∀ a k : ℕ, IsPairClass a k →
        classValue (hX 1 γ) (Real.tan (η / 2)) n a k =
          (((n : ℝ) - 8 + 2 * a + k) * Real.cos (3 * γ) +
              ((n : ℝ) - 2 - ((n : ℝ) - 8 + 2 * a + k)) * Real.cos γ) / Real.tan (η / 2) -
            Real.tan (η / 2) * (2 * (1 - (a : ℝ)) * Real.cos (3 * γ) +
              (2 - 2 * (1 - (a : ℝ))) * Real.cos γ)) ∧
      (∀ a k : ℕ, IsPairClass a k →
        classValue (hY γ) (Real.tan (η / 2)) n a k =
          ((3 * (k : ℝ) + 2 * a - 6) * Real.sin γ -
              ((n : ℝ) - 8 + 2 * a + k) * Real.sin (3 * γ)) / Real.tan (η / 2) +
            2 * Real.tan (η / 2) * ((a : ℝ) * Real.sin γ + (1 - (a : ℝ)) * Real.sin (3 * γ))) ∧
      (∀ a k : ℕ, IsPairClass a k →
        classValue (hX 2 γ) (Real.tan (η / 2)) n a k =
          (((n : ℝ) - 8 + 2 * a + k) * (Real.cos (3 * γ) + Real.cos (6 * γ)) +
              ((n : ℝ) - 2 - ((n : ℝ) - 8 + 2 * a + k)) * (Real.cos γ + Real.cos (2 * γ))) /
                Real.tan (η / 2) -
            Real.tan (η / 2) * (2 * (1 - (a : ℝ)) * (Real.cos (3 * γ) + Real.cos (6 * γ)) +
              (2 - 2 * (1 - (a : ℝ))) * (Real.cos γ + Real.cos (2 * γ)))) ∧
      (incrK (hX 1 γ) (Real.tan (η / 2)) = (Real.cos (3 * γ) - Real.cos γ) / Real.tan (η / 2) ∧
        incrK (hX 1 γ) (Real.tan (η / 2)) =
          -(4 * Real.cos γ * Real.sin γ ^ 2) / Real.tan (η / 2) ∧
        (incrK (hX 1 γ) (Real.tan (η / 2)) ≠ 0 →
          incrA (hX 1 γ) (Real.tan (η / 2)) / incrK (hX 1 γ) (Real.tan (η / 2)) =
            2 * (1 + Real.tan (η / 2) ^ 2))) ∧
      (incrK (hY γ) (Real.tan (η / 2)) = (3 * Real.sin γ - Real.sin (3 * γ)) / Real.tan (η / 2) ∧
        incrK (hY γ) (Real.tan (η / 2)) = 4 * Real.sin γ ^ 3 / Real.tan (η / 2) ∧
        (incrK (hY γ) (Real.tan (η / 2)) ≠ 0 →
          incrA (hY γ) (Real.tan (η / 2)) / incrK (hY γ) (Real.tan (η / 2)) =
            -((1 + Real.tan (η / 2) ^ 2) * Real.cos (2 * γ) / Real.sin γ ^ 2))) ∧
      (incrK (hX 2 γ) (Real.tan (η / 2)) =
          ((Real.cos (3 * γ) + Real.cos (6 * γ)) - (Real.cos γ + Real.cos (2 * γ))) /
            Real.tan (η / 2) ∧
        (incrK (hX 2 γ) (Real.tan (η / 2)) ≠ 0 →
          incrA (hX 2 γ) (Real.tan (η / 2)) / incrK (hX 2 γ) (Real.tan (η / 2)) =
            2 * (1 + Real.tan (η / 2) ^ 2))) ∧
      (ClassInjective (classValue (hX 1 γ) (Real.tan (η / 2)) n) ↔
        ((∀ z : ℤ, γ ≠ (z : ℝ) * (Real.pi / 2)) ∧ Real.tan (η / 2) ^ 2 ≠ 1 / 2)) ∧
      (ClassInjective (classValue (hX 2 γ) (Real.tan (η / 2)) n) ↔
        (Real.cos (3 * γ) + Real.cos (6 * γ) ≠ Real.cos γ + Real.cos (2 * γ) ∧
          Real.tan (η / 2) ^ 2 ≠ 1 / 2)) ∧
      (ClassInjective (classValue (hY γ) (Real.tan (η / 2)) n) ↔
        (Real.sin γ ≠ 0 ∧ ∀ z : ℤ, -3 ≤ z → z ≤ 2 →
          (1 + Real.tan (η / 2) ^ 2) * Real.cos (2 * γ) / Real.sin γ ^ 2 ≠ (z : ℝ))) := by sorry

end PhaseEncodedQGE.Supplement
