-- Prove2me | Theorems.Thm_RecruitSmaller_Supplement_theorem_1_5
-- name    : RecruitSmaller.Supplement.theorem_1_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T00:59:59.150909+00:00
-- url     : https://prove2.me/theorems/d4d6fd19-ef7c-42d9-93d3-23bf65cdeec1
-- title:
--   Theorem 1.5 — two-sided recruitment needs $\Omega(1/r)$ traders per side
-- statement:
--   Let $r\in(0,1)$, let $c\ge1$ be an integer with $c<\lceil\tfrac1{64r}\rceil$, and set $n:=\lceil\tfrac2{5r}\rceil$. Then for every prior-independent mechanism $M$ (deterministic or randomized) for $n+c$ buyers and $n+c$ sellers that is DSIC, IR and WBB, there exist distributions $F_B\succeq_r F_S$ on $[0,1]$ with $\mathrm{OPT}(n,n)>0$ such that
--   $$
--   \mathrm{GFT}_M(n+c,n+c)<\mathrm{OPT}(n,n). \tag{1.5}
--   $$
--   Here a **mechanism** for $m$ buyers and $k$ sellers assigns to every reported profile $(b,s)\in\mathbb R^m\times\mathbb R^k$ measurable expected allocation probabilities $x^B_j(b,s),x^S_\ell(b,s)\in[0,1]$ with $\sum_j x^B_j=\sum_\ell x^S_\ell$, and expected payments $p^B_j,p^S_\ell\in\mathbb R$; DSIC, IR and WBB are the dominant-strategy, ex-post and pointwise notions of §2.1, and $\mathrm{GFT}_M(m,k)$ is the expectation of $\sum_j b_jx^B_j-\sum_\ell s_\ell x^S_\ell$ under $F_B^m\times F_S^k$.
--
--   For $r\ge1/64$ no integer $c\ge1$ satisfies the hypothesis, so the statement has content for $r<1/64$, as on the page. It shows that recruiting on both sides cannot beat $\Theta(1/r)$ uniformly over market sizes.
--
--   Differences from the source:
--   - encoding: distributions (CDFs) on [0, 1] → probability measures μ on ℝ with μ [0, 1] = 1, CDF cdf μ; reason: every distribution on [0, 1] is exactly one such measure; same instances
--   - encoding: prior-independent mechanism (rules do not depend on F_B, F_S) → ∀ M, ∃ μB μS (the mechanism is quantified before the distributions); reason: a mechanism is a fixed function of the reports, so the quantifier order is prior independence
--   - encoding: randomized mechanism given by expected allocations and payments (§2.1) → structure Mechanism with expected allocations in [0, 1], feasibility Σ xB = Σ xS, jointly measurable allocations, real payments; reason: the page defines a mechanism by exactly these expected quantities; deterministic mechanisms are the {0,1}-valued case
--   - encoding: GFT_M < OPT with OPT a real expectation → OPT ≠ ⊤ ∧ Integrable gft_M ∧ GFT_M < OPT.toReal, with OPT the published ℝ≥0∞-valued RecruitSmaller.OPT and GFT_M a Bochner integral; reason: both clauses are automatic for laws on [0, 1] with measurable allocations in [0, 1]; stated so the Bochner and toReal junk values cannot make the comparison vacuous
--   - encoding: ⌈1/(64r)⌉ and n := ⌈2/(5r)⌉ (integer ceilings) → Nat.ceil of the positive reals 1/(64 r) and 2/(5 r); n a variable with hn : n = ⌈2/(5 r)⌉₊; reason: the arguments are positive, so natural and integer ceilings agree
-- source:
--   Cai–Gupta–Jiang–Liaw–Mehta–Velegkas–Wang–Zhao, The Power of Recruiting the Smaller Side: Two Additional Traders Suffice in Two-Sided Markets, arXiv:2609.27304 (held version, sha256 82900bb2…932a), Theorem 1.5, p.3 (PDF 5), eq. (1.5)

import Mathlib
import Definitions.Def_RecruitSmaller_OPT
import Definitions.Def_RecruitSmaller_Supplement_IsDSIC
import Definitions.Def_RecruitSmaller_Supplement_IsIR
import Definitions.Def_RecruitSmaller_Supplement_IsWBB
import Definitions.Def_RecruitSmaller_Supplement_GFT__8e3ec3

open MeasureTheory ProbabilityTheory

namespace RecruitSmaller.Supplement

/-- **Theorem 1.5 (Mechanism-Independent Ω(1/r) Lower Bound for Two-Sided Recruitment)**
(Cai–Gupta–Jiang–Liaw–Mehta–Velegkas–Wang–Zhao, *The Power of Recruiting the Smaller Side*, arXiv:2609.27304 (held version, sha256 82900bb2…932a), p.3, eq. (1.5); proof Appendix C.2): let `r ∈ (0, 1)` and let `c ∈ ℤ_{≥1}` satisfy
`c < ⌈1/(64r)⌉`, and set `n := ⌈2/(5r)⌉`. Then for every prior-independent mechanism `M`
(deterministic or randomized) for `n + c` buyers and `n + c` sellers that is DSIC, IR and WBB,
there exist distributions `F_B ⪰_r F_S` on `[0, 1]` with `OPT(n, n) > 0` such that
`GFT_M(n + c, n + c) < OPT(n, n)`.

**Formalization Note** "Distributions on [0, 1]" are probability measures `μ` on `ℝ` with
`μ [0, 1] = 1`, with CDFs `F = cdf μ`. Prior independence is the quantifier order: the mechanism is
fixed first and the distributions are chosen afterwards. `OPT` is the published `RecruitSmaller.OPT`
(valued in `ℝ≥0∞`); the conclusion also asserts `OPT(n, n) < ∞` and the integrability of `gft_M`
(both automatic on `[0, 1]`) so that the comparison of the real `GFT_M` with `OPT.toReal` is the
page's comparison. The ceilings are `Nat.ceil` of positive reals; `n` is a variable pinned by `hn`. For
`r ≥ 1/64` no `c` satisfies the hypothesis, exactly as on the page. -/
theorem theorem_1_5 (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) (c : ℕ) (hc1 : 1 ≤ c)
    (hc : c < ⌈1 / (64 * r)⌉₊) (n : ℕ) (hn : n = ⌈2 / (5 * r)⌉₊)
    (M : Mechanism (n + c) (n + c)) (hDSIC : IsDSIC M) (hIR : IsIR M) (hWBB : IsWBB M) :
    ∃ μB μS : Measure ℝ, IsProbabilityMeasure μB ∧ IsProbabilityMeasure μS ∧
      μB (Set.Icc 0 1) = 1 ∧ μS (Set.Icc 0 1) = 1 ∧
      (∀ x, r * (1 - cdf μS x) ≤ 1 - cdf μB x) ∧
      0 < OPT n n μB μS ∧ OPT n n μB μS ≠ ⊤ ∧
      Integrable (fun ω : (Fin (n + c) → ℝ) × (Fin (n + c) → ℝ) => gft M ω.1 ω.2)
        ((Measure.pi fun _ : Fin (n + c) => μB).prod (Measure.pi fun _ : Fin (n + c) => μS)) ∧
      GFT M μB μS < (OPT n n μB μS).toReal := by sorry

end RecruitSmaller.Supplement
