-- Prove2me | Theorems.Thm_PhaseEncodedQGE_theorem_3_2
-- name    : PhaseEncodedQGE.theorem_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:52:40.697378+00:00
-- url     : https://prove2.me/theorems/391f9362-86b3-4cc5-84ea-ca91badffe60
-- title:
--   Theorem 3.2 (= Theorem A.4) — layer template $\lambda(x)=t^{-1}\sum_{j\notin D}h(k_j(D))-t\sum_{j\in D}h(k_j(D))$
-- statement:
--   Let $G$ be a cubic graph on $n$ vertices with the degree-aware preparation and $t=\tan(\eta/2)$. Define the mixer profiles $h^{X,r}(k)=\sum_{b=1}^r\cos(b\gamma(2k-3))$ and $h^Y(k)=\sin(\gamma(2k-3))$. For every outcome $x$ with defect set $D$,
--   $$\lambda(x)=\frac1t\sum_{j\notin D}h\bigl(k_j(D)\bigr)-t\sum_{j\in D}h\bigl(k_j(D)\bigr),$$
--   with $h=h^{X,r}$ for the X mixer at $r\ge1$ tied repetitions and $h=h^Y$ for the Y mixer at one repetition. Under the Hadamard preparation with one X mixer, $p_0=2^{-n}$ and
--   $$p_1(x)=2^{-n}\Bigl[\sum_{j\in D}\sin\bigl(\gamma(2k_j-3)\bigr)-\sum_{j\notin D}\sin\bigl(\gamma(2k_j-3)\bigr)\Bigr].$$
--
--   The first-order value of every outcome is therefore a linear functional of the profile of its defect set; this is the template from which the determination theorems follow.
--
--   Differences from the source:
--   - encoding: $\lambda=p_1/p_0$ and $t^{\pm1}$ used without comment → hypotheses $\cos(\eta/2)\ne0$ and $\sin(\eta/2)\ne0$; reason: they exclude only the angles at which t, 1/t or p₁/p₀ is undefined (Lean's x/0 = 0 would otherwise give junk values)
-- source:
--   Miller, Lee, Structural Accessibility in Phase-Encoded Quantum Graph Embeddings, STOC 2027 submission (build 2026-11-03, sha256 f1132658…7c51), §3.1, p.6 (PDF p.7), Theorem 3.2, eqs. (8)–(10) (= Theorem A.4, p.14, eqs. (22)–(25))

import Mathlib
import Definitions.Def_PhaseEncodedQGE_Circuit
import Definitions.Def_PhaseEncodedQGE_Profile
set_option autoImplicit false

namespace PhaseEncodedQGE

open Matrix

/-- Theorem 3.2 (= Theorem A.4), the layer template (Miller, Lee, *Structural Accessibility in Phase-Encoded Quantum Graph Embeddings*, STOC 2027 submission (build 2026-11-03), §3.1, p.6, eqs. (9)–(10); App. A.1.1, p.14,
eqs. (22)–(25)).

Let `G` be a simple cubic graph with the degree-aware preparation, `t = tan(η/2)`. For every
outcome `x` with defect set `D`,
`λ(x) = (1/t) ∑_{j∉D} h(k_j(D)) − t ∑_{j∈D} h(k_j(D))`,
with `h = h^{X,r}` for the X mixer at `r` tied repetitions and `h = h^Y` for the Y mixer at one
repetition. Under the Hadamard preparation with one X mixer, `p₀ = 2^{−n}` and
`p₁(x) = 2^{−n}[∑_{j∈D} sin(γ(2k_j − 3)) − ∑_{j∉D} sin(γ(2k_j − 3))]`.

**Formalization Note** `λ` is `firstOrder`, `p₀` is `born … 0`, `p₁` is `bornDeriv`. The
hypotheses `cos(η/2) ≠ 0` and `sin(η/2) ≠ 0` only exclude the angles at which `t^{±1}` or `p₁/p₀`
is undefined. -/
theorem theorem_3_2 (n : ℕ) (G : SimpleGraph (Fin n)) (hG : IsCubic G) (γ : ℝ) :
    (∀ (η : ℝ), Real.cos (η / 2) ≠ 0 → Real.sin (η / 2) ≠ 0 → ∀ (r : ℕ), 1 ≤ r →
      ∀ x : Outcome n,
        firstOrder (degPrep G η) .X r G γ x =
          (Real.tan (η / 2))⁻¹ * ∑ j ∈ Finset.univ \ defects x, hX r γ (kdef G (defects x) j) -
            Real.tan (η / 2) * ∑ j ∈ defects x, hX r γ (kdef G (defects x) j)) ∧
    (∀ (η : ℝ), Real.cos (η / 2) ≠ 0 → Real.sin (η / 2) ≠ 0 → ∀ x : Outcome n,
        firstOrder (degPrep G η) .Y 1 G γ x =
          (Real.tan (η / 2))⁻¹ * ∑ j ∈ Finset.univ \ defects x, hY γ (kdef G (defects x) j) -
            Real.tan (η / 2) * ∑ j ∈ defects x, hY γ (kdef G (defects x) j)) ∧
    (∀ x : Outcome n,
        born (hadPrep n) .X 1 G γ 0 x = (2 : ℝ)⁻¹ ^ n ∧
        bornDeriv (hadPrep n) .X 1 G γ x =
          (2 : ℝ)⁻¹ ^ n *
            (∑ j ∈ defects x, Real.sin (γ * (2 * (kdef G (defects x) j : ℝ) - 3)) -
              ∑ j ∈ Finset.univ \ defects x, Real.sin (γ * (2 * (kdef G (defects x) j : ℝ) - 3))))
    := by sorry

end PhaseEncodedQGE
