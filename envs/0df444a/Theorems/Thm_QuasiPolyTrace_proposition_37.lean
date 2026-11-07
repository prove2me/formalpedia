-- Prove2me | Theorems.Thm_QuasiPolyTrace_proposition_37
-- name    : QuasiPolyTrace.proposition_37
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:32:52.805957+00:00
-- url     : https://prove2.me/theorems/1a99892b-9497-448e-a1d9-c17903138f89
-- title:
--   Proposition 37 — the induction step: zoom out from $R$ to $R'\in[3R^{1.1},R^2]$
-- statement:
--   There are universal constants $C>0$ and $R_0$ such that the following holds. Let $x,y\in\{0,1\}^n$ have first discrepancy $d$, let $p\in(0,\tfrac1{12}]$, let $R\ge R_0$ be an integer, and let $\tau>0$ and $k$ satisfy
--
--   $$
--   4k\log R\le\log(1/\tau)\le R^{0.8}p^2 .
--   $$
--
--   Let $s$ be a statistic of $k$ integers in $\{1,\dots,\sigma\}$ with $\min s=1$, where $\sigma\le\sqrt{Rp\log(1/\tau)}$, and let an integer $\ell\le2Rp+\sqrt{Rp\log(1/\tau)}$ satisfy
--
--   $$
--   \big|x^{(s+\ell)}_{[d-2R:n],p}-y^{(s+\ell)}_{[d-2R:n],p}\big|\ge\tau .
--   $$
--
--   Then there are an integer $R'\in[3R^{1.1},R^2]$, $P\in[p,3p]$, $\tau'\ge\tau^C$, a statistic $S$ of order at most $3k$ with $\min S=1$ and span at most $\sqrt{\tfrac12R'P\log(1/\tau')}$, with
--
--   $$
--   12k\log R'\le\log(1/\tau')\le(R'/2)^{0.8}P^2,
--   $$
--
--   and an integer $\ell'\le R'P+\sqrt{\tfrac12R'P\log(1/\tau')}$ such that
--
--   $$
--   \big|x^{(S+\ell')}_{[d-R-R':n],P}-y^{(S+\ell')}_{[d-R-R':n],P}\big|\ge\tau' .
--   $$
--
--   Windows starting at a position $\le0$ are padded with zeros on the left. Each step squares the window around the first discrepancy at the cost of a polynomial loss in $\tau$, tripling the order and at most tripling the retention probability.
--
--   Differences from the source:
--   - reading: τ′ ≥ 1/poly(1/τ); R larger than some universal constant → τ′ ≥ τ^C with C > 0 and the threshold R₀ universal, chosen before the strings, p, R, τ, k; reason: the proof of Theorem 44 uses the proposition in exactly this form (p.43: "a constant C … so that in each iteration τ′ ≥ τ^C"); the proof sets τ′ = τ^{c_f}
--   - generalization: an order ≤ 3k statistic S of span ≤ √(½R′P log(1/τ′)) → additionally min S = 1 (1 ∈ S); reason: the proof constructs S "as having min value 1" (Lemma 40, p.37; p.39), and the next application of the proposition (proof of Theorem 44) requires it; the Lean statement implies the printed one
--   - encoding: windows x[d−2R:n], x[d−R−R′:n] with possibly non-positive start → window (zero-padded on the left); reason: the padding convention of the proof of Theorem 44, p.42
--   - encoding: τ with log(1/τ) defined → 0 < τ; reason: log(1/τ) is the paper's notation for a positive discrepancy bound; it excludes only the undefined case
-- source:
--   Burudgunte, Valiant, Wang, Quasipolynomial Trace Reconstruction, manuscript of November 2, 2026 (later version of arXiv:2607.04073; sha256 9ecb6d18…), Proposition 37, p.34 (with Lemma 40, p.37, and pp.39, 43)

import Mathlib
import Definitions.Def_TraceReconstruction
import Definitions.Def_QuasiPolyTrace_stat
import Definitions.Def_QuasiPolyTrace_shift
import Definitions.Def_QuasiPolyTrace_window
import Definitions.Def_QuasiPolyTrace_IsFirstDiscrepancy

namespace QuasiPolyTrace

open OAI.TraceReconstruction

/-- **Proposition 37 (the induction step: quadratic zoom-out).** Burudgunte, Valiant, Wang, *Quasipolynomial Trace Reconstruction*, manuscript of November 2, 2026
(later version of arXiv:2607.04073; sha256 9ecb6d18…), Proposition 37, p.34: "Given
n-bit strings x, y where d = min{i : x_i ≠ y_i} is the point of first discrepancy, and a retention
probability p ∈ (0, 1/12]. For integer R larger than some universal constant, if τ satisfies
4k log R ≤ log(1/τ) ≤ R^{0.8}p² and if there exists a statistic s consisting of k integers in {1, …, σ}
with min_i s_i = 1, where σ ≤ √(Rp log(1/τ)) ('s has order k and span σ') such that for some integer
ℓ ≤ 2Rp + √(Rp log(1/τ)) we have |x^{(s+ℓ)}_{[d−2R:n],p} − y^{(s+ℓ)}_{[d−2R:n],p}| ≥ τ then: there
exists an integer R′ ∈ [3R^{1.1}, R²] and a probability P ∈ [p, 3p] and a bound τ′ ≥ 1/poly(1/τ) for
which there is an order ≤ 3k statistic S of span ≤ √(½R′P log(1/τ′)) and
12k log R′ ≤ log(1/τ′) ≤ (R′/2)^{0.8}P² and a location ℓ′ ≤ R′P + √(½R′P log(1/τ′)) for which
|x^{(S+ℓ′)}_{[d−R−R′:n],P} − y^{(S+ℓ′)}_{[d−R−R′:n],P}| ≥ τ′."

**Formalization Note.**
* "1/poly(1/τ)" is `τ^C` for a universal exponent `C > 0`, chosen with the universal threshold `R₀`
  before everything else; this is how the proof of Theorem 44 uses it (p.43: "we can thus find a constant
  C … so that in each iteration τ′ ≥ τ^C"). In the proof (p.39), `τ′ := τ^{c_f}` for a constant `c_f`.
* Windows that start at `d − 2R ≤ 0` or `d − R − R′ ≤ 0` are zero-padded on the left (`window`), the
  convention of the proof of Theorem 44 (p.42).
* A statistic is a finite set of integers, its order is its cardinality, "span ≤ σ" means every entry lies
  in `{1, …, ⌊σ⌋}`, and `s + ℓ` is `shift s ℓ`.
* `τ > 0` is assumed: `log(1/τ)` is the paper's notation for a positive discrepancy bound.
* The conclusion also states `min S = 1` (`1 ∈ S`): the proof constructs `S` "as having min value 1"
  (Lemma 40, p.37, and p.39), and the next application of the proposition in Theorem 44 needs it.
* Logarithms are natural. -/
theorem proposition_37 :
    ∃ C R₀ : ℝ, 0 < C ∧ ∀ (n : ℕ) (x y : Word n) (d : ℕ), IsFirstDiscrepancy x y d →
      ∀ (p : ℝ), 0 < p → p ≤ 1 / 12 → ∀ (R : ℕ), R₀ ≤ R →
      ∀ (τ : ℝ) (k : ℕ), 0 < τ →
      4 * k * Real.log R ≤ Real.log (1 / τ) → Real.log (1 / τ) ≤ (R : ℝ) ^ (0.8 : ℝ) * p ^ 2 →
      ∀ s : Finset ℤ, s.card = k → 1 ∈ s →
      (∀ i ∈ s, 1 ≤ i ∧ (i : ℝ) ≤ Real.sqrt (R * p * Real.log (1 / τ))) →
      ∀ ℓ : ℤ, (ℓ : ℝ) ≤ 2 * R * p + Real.sqrt (R * p * Real.log (1 / τ)) →
      τ ≤ |stat p (window (List.ofFn x) ((d : ℤ) - 2 * R)) (shift s ℓ)
          - stat p (window (List.ofFn y) ((d : ℤ) - 2 * R)) (shift s ℓ)| →
      ∃ R' : ℕ, 3 * (R : ℝ) ^ (1.1 : ℝ) ≤ R' ∧ R' ≤ R ^ 2 ∧
      ∃ P : ℝ, p ≤ P ∧ P ≤ 3 * p ∧
      ∃ τ' : ℝ, τ ^ C ≤ τ' ∧
      ∃ S : Finset ℤ, S.card ≤ 3 * k ∧ 1 ∈ S ∧
        (∀ i ∈ S, 1 ≤ i ∧ (i : ℝ) ≤ Real.sqrt (1 / 2 * R' * P * Real.log (1 / τ'))) ∧
        12 * k * Real.log R' ≤ Real.log (1 / τ') ∧
        Real.log (1 / τ') ≤ ((R' : ℝ) / 2) ^ (0.8 : ℝ) * P ^ 2 ∧
      ∃ ℓ' : ℤ, (ℓ' : ℝ) ≤ R' * P + Real.sqrt (1 / 2 * R' * P * Real.log (1 / τ')) ∧
        τ' ≤ |stat P (window (List.ofFn x) ((d : ℤ) - R - R')) (shift S ℓ')
            - stat P (window (List.ofFn y) ((d : ℤ) - R - R')) (shift S ℓ')| := by sorry

end QuasiPolyTrace
