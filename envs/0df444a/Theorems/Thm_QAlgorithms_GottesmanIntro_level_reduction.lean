-- Prove2me | Theorems.Thm_QAlgorithms_GottesmanIntro_level_reduction
-- name    : QAlgorithms.GottesmanIntro.level_reduction
-- status  : Open
-- author  : @Goku
-- created : 2026-10-13T18:05:17.299862+00:00
-- url     : https://prove2.me/theorems/a90b7981-d420-4516-a000-b63c3002a613
-- title:
--   Level reduction: a local stochastic model on C′ induces one on C with bounds Σ_{|R|=t+1} Π p_j
-- statement:
--   Fix an $[[n,1,2t+1]]$ code with fault-tolerant gadgets of a common depth (Definitions 2–5), a circuit $C$ as in Definition 6, and its fault-tolerant circuit $C'$. Suppose $C'$ undergoes a local stochastic error model (Definition 12): with probability $p_S$ the faults are at precisely the set $S$ of locations of $C'$, the errors there being arbitrary quantum operations, possibly entangled through an environment, applied in chronological order; and for every set $R$ of locations,
--
--   $$\sum_{S\supseteq R} p_S \le \prod_{j\in R} p_j,\qquad p_j<1.$$
--
--   For a location $C_i$ of $C$ put
--
--   $$p'_i = \sum_{R} \prod_{j\in R} p_j,$$
--
--   the sum over the sets $R$ of exactly $t+1$ locations of $C'$ contained in the extended rectangle of $C_i$. Then there is an error model on $C$ such that
--
--   1. faults occur at precisely the set $S'$ of locations of $C$ with probability $\sum_{S:\,\mathrm{bad}(S)=S'} p_S$, where $\mathrm{bad}(S)$ is the set of bad ExRecs assigned by Definition 10;
--   2. the decoded output distribution of $C'$ equals the output distribution of $C$ under this model;
--   3. the model is local stochastic with error bounds $p'_i$: for every set $R$ of locations of $C$, the probability of faults at all of $R$ is at most $\prod_{i\in R} p'_i$;
--   4. if $0\le p$ and $p_j\le p$ for all locations $j$ of $C'$, then $p'_i\le A\,p^{t+1}$ for every location $C_i$, where $A$ is the maximum over the types of ExRecs of the number of $(t+1)$-element sets of locations of the ExRec.
--
--   This is the step that lets concatenation reduce the error rate from $p$ to $A p^{t+1}$ per level.
--
--   **Formalization Note** The side condition $p'_i<1$ of Definition 12 is not claimed (eq. (84) can exceed $1$); the local stochastic inequality is stated with the bounds $p'_i$ exactly.
-- source:
--   Daniel Gottesman, An Introduction to Quantum Error Correction and Fault-Tolerant Quantum Computation, 2009, v1, PDF p. 40, Theorem 9. https://arxiv.org/pdf/0904.2557v1

import Definitions.Def_QAlgorithms_Defs_FTCircuit
import Definitions.Def_QAlgorithms_GottesmanIntro_Ch05b_Model
set_option autoImplicit false

namespace QAlgorithms.GottesmanIntro





/-- Gottesman intro p.40, Theorem 9 (Level Reduction): "Suppose we have a fault-tolerant circuit
`C′` for `C`, and suppose `C′` experiences a local stochastic error model with error bounds `p_i`
and probability `p_S` of errors at precisely the set `S` of locations. Then for any particular set
`S` define `C̃_S` as in theorem 8, and define an error model on `C` by replacing `C` with `C̃_S`
with probability `p_S`. This is a local stochastic error model. The error bounds `p′_i` for `C`
are given by `p′_i ≤ Σ_R Π_{i∈R} p_i` (84) … In the special case where `p_i ≤ p` for all `i`, we
have `p′_i ≤ A p^{t+1}` (85)."

Let `P` be a fault-tolerant protocol, `C` a Def. 6 circuit, and `M` a local stochastic error
model (Def. 12: arbitrary chronological quantum errors, possibly entangled through an environment,
at a random set of faulty locations) on `C′ = ftCircuit P C` with bounds `p_i < 1`. Then there is
an error model `M′` on `C` such that
1. faults occur at precisely the set `S′` of locations of `C` with probability
   `Σ_{S : bad(S) = S′} p_S`, `bad(S)` the bad locations of Def. 10;
2. the decoded output distribution of `C′` under `M` equals the output distribution of `C` under
   `M′`;
3. `M′` is local stochastic with the bounds `p′_i` of eq. (84);
4. if `0 ≤ p` and `p_j ≤ p` for every location `j` of `C′`, then `p′_i ≤ A p^{t+1}` for every location `i`
   of `C`, with `A` as in eq. (85). -/
theorem level_reduction (P : FTProtocol) (hP : P.IsFaultTolerant) (hdepth : P.HasUniformDepth)
    {N : ℕ} (C : LocCircuit N) (hC : C.IsIdealCircuit)
    (M : LocalStochasticModel (N * (P.n + P.A))) (p : ℕ × ℕ → ℝ)
    (hp1 : ∀ j ∈ (ftCircuit P C).locs, p j < 1) (hM : IsLocalStochastic (ftCircuit P C) M p) :
    ∃ M' : LocalStochasticModel N,
      (∀ S' : Finset (ℕ × ℕ), M'.prob S' =
        ∑ S ∈ (ftCircuit P C).locs.powerset.filter (fun S => badAssignment P C S = S'),
          M.prob S) ∧
      pushDist (ftDecode P C) (noisyOutDist (ftCircuit P C) M) = noisyOutDist C M' ∧
      IsLocalStochastic C M' (levelReducedBound P C p) ∧
      ∀ p0 : ℝ, 0 ≤ p0 → (∀ j ∈ (ftCircuit P C).locs, p j ≤ p0) →
        ∀ i ∈ C.locs, levelReducedBound P C p i ≤ (exRecSubsetMax P : ℝ) * p0 ^ (P.t + 1) := by
  sorry


end QAlgorithms.GottesmanIntro
