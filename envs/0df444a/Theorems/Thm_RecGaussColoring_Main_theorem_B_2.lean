-- Prove2me | Theorems.Thm_RecGaussColoring_Main_theorem_B_2
-- name    : RecGaussColoring.Main.theorem_B_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:25:48.735223+00:00
-- url     : https://prove2.me/theorems/4e717b7e-6abc-456f-9047-3a124027f2df
-- title:
--   Theorem B.2 — deterministic and randomized progress combination
-- statement:
--   Fix $\alpha,\beta\in(0,1)$ and write $f_k(n)=n^\alpha(\log(n+2))^k$. The following two implications hold.
--
--   1. If some fixed $k\in\mathbb N$ and $C>0$ admit deterministic polynomial-time Blum progress routines at scale $f_k$ for both three-colorable domains $\Delta\le n^\beta$ and $\delta\ge n^\beta$, then some $k'$ and $C'>0$ admit a deterministic polynomial-time proper coloring of every three-colorable graph with at most $C'f_{k'}(n)$ colors.
--   2. If some fixed $k,C>0,n_0$ admit a randomized P1 routine on the sparse domain and a deterministic P1/P2/P3 progress routine on the dense domain, both for $n\ge n_0$, then some $k'$ and $C'>0$ admit a randomized polynomial-time proper coloring of every three-colorable graph with at most $C'f_{k'}(n)$ colors, with success probability at least $1-1/n$.
--
--   In each clause the quantitative target is
--   $$
--   \#\text{colors}\le C'n^\alpha(\log(n+2))^{k'}.
--   $$
--   The randomized hypothesis is restricted to checkable P1 outputs, matching Theorem 1.5. This result supplies the combination in Appendix B; the printed deterministic clause is retained alongside the form used there.
--
--   Differences from the source:
--   - encoding: Õ(n^α) and polynomial-time routines → existential natural logarithmic powers and positive constants, with the published integer RAM; reason: log(n+2) avoids undefined small-size logarithms without changing the Õ bound
--   - reading: polynomial-time progress as printed and the randomized application on p. 26 → a conjunction of the deterministic implication and the implication with randomized sparse P1 progress and deterministic dense progress; reason: this retains the printed assertion and the exact form applied to Theorem 1.5; its external KT17 reduction remains proof work
--   - generalization: progress available on each whole degree-restricted class → the randomized clause allows progress routines guaranteed only for n≥n₀; reason: the source’s application itself uses sufficiently large n; a fixed finite set of smaller sizes can be handled separately
--   - reading: with high probability → success fraction at least 1−1/n; at n=0 success is one; reason: this is the shared RAM convention; the output is checkable and the empty graph is handled exactly
-- source:
--   Ijay Narang, Yukai Tang, STOC 2027 submission #295 (October 2026), Theorem B.2 and its application in the proof of Theorem 1.1, p. 26. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/295.pdf

import Definitions.Def_RecGaussColoring_Main_Progress

open scoped RealInnerProductSpace
open Filter MeasureTheory ProbabilityTheory
open scoped Topology
noncomputable section

namespace RecGaussColoring.Main

/-- Theorem B.2, p. 26: printed deterministic form and randomized-P1 form used there. -/
theorem theorem_B_2 (α β : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (hβ0 : 0 < β) (hβ1 : β < 1) :
  ((∃ k : ℕ, ∃ C : ℝ, 0 < C ∧
      CongruencyTU.DetSolves encGraph graphSize (SparseDomain β 0)
        (fun I out => IsProgress C (softPower α k I.n) I out) ∧
      CongruencyTU.DetSolves encGraph graphSize (DenseDomain β 0)
        (fun I out => IsProgress C (softPower α k I.n) I out)) →
    ∃ k' : ℕ, ∃ C' : ℝ, 0 < C' ∧
      CongruencyTU.DetSolves encGraph graphSize ThreeColorable
        (fun I out => GoodColoring I out (C'*softPower α k' I.n))) ∧
  ((∃ k : ℕ, ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ,
      CongruencyTU.RandSolves encGraph graphSize (SparseDomain β n₀)
        graphSize (fun _ => True)
        (fun I out => IsProgressP1 C (softPower α k I.n) I out) ∧
      CongruencyTU.DetSolves encGraph graphSize (DenseDomain β n₀)
        (fun I out => IsProgress C (softPower α k I.n) I out)) →
    ∃ k' : ℕ, ∃ C' : ℝ, 0 < C' ∧
      CongruencyTU.RandSolves encGraph graphSize ThreeColorable graphSize (fun _ => True)
        (fun I out => GoodColoring I out (C'*softPower α k' I.n))) := by sorry

end RecGaussColoring.Main
