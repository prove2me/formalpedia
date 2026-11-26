-- Prove2me | Theorems.Thm_ReusableMatching_Supplement_theorem_2
-- name    : ReusableMatching.Supplement.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-26T22:06:48.714328+00:00
-- url     : https://prove2.me/theorems/1afbf829-c6e2-4ee6-b56d-9f888460b486
-- title:
--   Theorem 2 — OPD with Algorithm 2 is $50/99$-competitive
-- statement:
--   Let a vertex-weighted OBMRR instance be given. At each arrival, let Algorithm 3 choose any set of at most two current neighbors that maximizes its exact dual value $\beta_j$, and use Algorithm 2 as the OCR subroutine. With
--
--   $$
--   \gamma=\frac1{32},\qquad \beta_1=\frac{50}{99},\qquad \beta_2=\frac{16}{33},
--   $$
--
--   the resulting algorithm has all three properties of an online competitive algorithm:
--
--   1. for every coin outcome its output is a feasible reusable matching;
--   2. its decisions through arrival $j$ depend only on edges and random coins through $j$;
--   3. its expected reward satisfies
--
--   $$
--   \mathbb E[\operatorname{reward}(\mathrm{OPD})]\ge \frac{50}{99}\,\mathrm{OPT}.
--   $$
--
--   Here $\mathrm{OPT}$ is the integral offline optimum of the same instance.
--
--   **Formalization Note** The selector can choose any true maximizer, covering every tie choice allowed by Algorithm 3. Empty proposals are allowed. The expectation is a finite uniform average over Algorithm 2's independent fair coins.
--
--   Differences from the source:
--   - reading: the theorem prints $\Gamma\approx0.505$ → Lean states the exact $\Gamma=50/99$ established on p.26; reason: the proof computes $(3+4/32)/(6+6/32)=50/99\approx0.50505$.
--   - generalization: Algorithm 3 says to find a maximizing set but gives no tie rule → Lean quantifies over every selector function (of the proposal history and current neighbor set, but chosen with the whole instance in view) that picks some maximizer along the run; reason: the proof uses only maximality, and every online tie rule is such a selector.
--   - reading: Algorithm 3 asks for a set $Q_j\subseteq N(j)$ "with the size at most two" while §4.1.1 lets OCR proposals have one or two vertices → Lean lets the empty set compete (a round with $Q_j=\emptyset$ proposes nothing and changes no OCR state); reason: it is forced when $N(j)=\emptyset$, and otherwise $\emptyset$ has $\beta_j=0\le$ every nonempty candidate, so it is chosen only on a tie at $0$.
--   - encoding: the paper uses one-based arrivals and fresh fair random choices → Lean uses `Fin n`, zero-based lists, and a finite independent three-bit tape; reason: the availability boundary and distribution are unchanged.
-- source:
--   Delong, Farhadi, Niazadeh, Sivan & Udwani, Online Bipartite Matching with Reusable Resources, arXiv:2110.07084v2, Theorem 2, p.4; Algorithms 2–3, pp.17, 24; exact ratio, p.26

import Mathlib
import Definitions.Def_ReusableMatching_Supplement_OPDMatching

namespace ReusableMatching.Supplement

set_option autoImplicit false

/-- **Theorem 2 (Main Result II)** of Delong, Farhadi, Niazadeh, Sivan & Udwani, *Online
Bipartite Matching with Reusable Resources*, arXiv:2110.07084v2, p.4 (proof pp.23–26).

For every vertex-weighted OBMRR instance and every rule that chooses a maximizing proposal in
Algorithm 3, OPD with Algorithm 2 as its OCR subroutine:
1. returns a feasible reusable matching for every coin outcome;
2. is online—decisions through round `j` use only edges and coins through `j`;
3. has expected reward at least `(50/99) · OPT`.

**Formalization Note.** The proof fixes `γ = 1/32`, `β₁ = 50/99`, and `β₂ = 16/33` on p.26.
The exact guarantee `50/99 ≈ 0.50505` is the full value behind the theorem's rounded
`Γ ≈ 0.505`.  Algorithm 3 leaves maximizing ties unspecified, so `select` is arbitrary subject
to `IsOPDSelector`; its type exposes only the proposal history and the current neighbor set.  The
expectation is the literal average over the finite independent fair-coin tape. -/
theorem theorem_2 {V : Type*} [Fintype V] [LinearOrder V] {n : ℕ}
    (I : ReusableMatching.OBMRRInstance V n) (select : OPDSelector V)
    (hselect : IsOPDSelector I (50 / 99 : ℝ) (16 / 33 : ℝ) select) :
    (∀ ω : Fin n → OCRCoins,
      ReusableMatching.IsFeasibleMatching I (OPDMatching I select ω)) ∧
    IsOnlineOPD I select ∧
    (50 / 99 : ℝ) * ReusableMatching.OPT I ≤ expectedOPDReward I select := by sorry

end ReusableMatching.Supplement
