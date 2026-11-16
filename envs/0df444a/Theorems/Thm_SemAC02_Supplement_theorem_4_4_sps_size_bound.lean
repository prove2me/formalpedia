-- Prove2me | Theorems.Thm_SemAC02_Supplement_theorem_4_4_sps_size_bound
-- name    : SemAC02.Supplement.theorem_4_4_sps_size_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T19:49:09.747096+00:00
-- url     : https://prove2.me/theorems/6cdf3d32-33e2-4115-ab39-077aa75faa37
-- title:
--   Theorem 4.4 — size bound for ΣΠΣ-PC via a pseudo-reduction operator
-- statement:
--   Let $F\subseteq B_n=B_n(\mathbb F_2)$ and let $d_0$ be the maximum degree of the polynomials in $F$. Fix $1\le k\le n$ and $1\le r\le n$, and put $B=3(k+\max\{d_0,r\})$. Suppose that $B\le n$ and that $R:B_n^{\le B}\to W$ is a degree-$B$ pseudo-reduction operator for $F$, and let $R_{\le k}$ be its restriction to $B_n^{\le k}$. Then every arity-2 semantic ΣΠΣ-PC refutation $\pi$ of $F$ satisfies
--
--   $$
--   S(\pi)\ \ge\ \frac{\operatorname{rank}(R_{\le k})}{2\binom{n-r}{k}}.
--   $$
--
--   This converts rank estimates for pseudo-reduction operators into size lower bounds for semantic ΣΠΣ-PC; it is applied to random 3-CNFs (Theorem 6.5) and the functional graph PHP (Theorem 6.12).
--
--   **Formalization Note** Elements of $B_n$ are their multilinear representatives. $W$ is any $\mathbb F_2$-vector space.
--
--   Differences from the source:
--   - encoding: proof lines are displayed circuits representing classes in B_n; initial lines are the axioms → ACirc terms; a line is an axiom line when its value on the cube equals an axiom; initial lines equal to 0 are allowed; reason: p.15: a line represents its residue class; p.54: initial tautologies 0 = 0; a zero line follows from any line, so no refutation or measure changes
--   - generalization: d₀ is the maximum degree of the polynomials in F → d₀ is any upper bound on these degrees; reason: for the maximum d ≤ d₀, restricting a degree-B′ operator to degree B ≤ B′ gives a degree-B operator with the same R_{≤k}, so the source's statement implies this one
--   - encoding: F ⊆ B_n → F a set of multilinear polynomials over ZMod 2; reason: multilinear representatives of B_n
-- source:
--   Alekseev, Gryaznov, Itsykson, Pitassi, Robere, Tzameret, Hard Instances for Strong Semantic Proof Systems: CNFs for Depth-Four PC and Deep Instances for AC0[2]-Frege, manuscript (STOC 2027 submission, sha256 c228d68b89b45b5c6c547aa994f7d1799441bb22b2a85e36c6cd400bea8cdb6a), Theorem 4.4, p.26 (PDF p.28)

import Mathlib
import Definitions.Def_AC02Frege_ML
import Definitions.Def_SemAC02_Ble
import Definitions.Def_SemAC02_Supplement_ACirc
import Definitions.Def_SemAC02_Supplement_IsSemPCRef
import Definitions.Def_SemAC02_Supplement_IsPseudoRed

namespace SemAC02.Supplement

open ACirc

/-- **Theorem 4.4 (Size bound for ΣΠΣ-PC via a reduction operator)** (Alekseev–Gryaznov–Itsykson–
Pitassi–Robere–Tzameret, *Hard Instances for Strong Semantic Proof Systems*, manuscript (STOC 2027
submission), Theorem 4.4, p.26): let `F ⊆ B_n`, and let `d₀` denote the maximum degree of the
polynomials in `F`. Fix `1 ≤ k, r ≤ n`, and put `B = 3(k + max{d₀, r})`. Suppose that `B ≤ n` and
that `R : B_n^{≤B} → W` is a degree-`B` pseudo-reduction operator for `F`, and write `R_{≤k}` for
the restriction of `R` to `B_n^{≤k}`. Then every semantic ΣΠΣ-PC refutation `π` of `F` satisfies
`S(π) ≥ rank(R_{≤k}) / (2 C(n − r, k))`.

**Formalization Note** Elements of `B_n = B_n(𝔽₂)` are their multilinear representatives; `d₀` is
any upper bound on the degrees of the polynomials of `F` (the maximum is one). `W` is any
`𝔽₂`-vector space. -/
theorem theorem_4_4_sps_size_bound {n : ℕ} (F : Set (MvPolynomial (Fin n) (ZMod 2))) (d₀ : ℕ)
    (hF : ∀ f ∈ F, AC02Frege.IsMultilinear f ∧ f.totalDegree ≤ d₀)
    (k r : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) (hr : 1 ≤ r) (hrn : r ≤ n)
    (hB : 3 * (k + max d₀ r) ≤ n)
    {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    (R : Ble (Fin n) (3 * (k + max d₀ r)) →ₗ[ZMod 2] W) (hR : IsPseudoRed F R)
    (π : List (ACirc (ZMod 2) (Fin n))) (hπ : IsSemPCRef IsSPS Set.univ (polyAx F) π) :
    (rankLe R k : ℝ) / (2 * ((n - r).choose k : ℝ)) ≤ topS Set.univ π := by sorry

end SemAC02.Supplement
