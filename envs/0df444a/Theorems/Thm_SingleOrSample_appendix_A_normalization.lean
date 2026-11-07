-- Prove2me | Theorems.Thm_SingleOrSample_appendix_A_normalization
-- name    : SingleOrSample.appendix_A_normalization
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:49:25.59896+00:00
-- url     : https://prove2.me/theorems/6a7eaaf9-4e98-4b28-8965-cc458df1a593
-- title:
--   Appendix A — normalization of valuation functions
-- statement:
--   Let $v$ be a function with $\mathrm{MMS}_v>0$ (for $n$ bundles), and let $v'=v/\mathrm{MMS}_v$. Then:
--
--   1. $\mathrm{MMS}_{v'}=1$;
--   2. for every bundle $B$ and every $\alpha$: $v'(B)\ge\alpha$ if and only if $v(B)\ge\alpha\,\mathrm{MMS}_v$;
--   3. $v'$ is a valuation if $v$ is, and submodular if $v$ is;
--   4. $v'$ and $v$ rank sets, and marginal values given any set, in the same way;
--   5. a strategy is safe for $v$ at target $\tau\,\mathrm{MMS}_v$ if and only if it is safe for $v'$ at target $\tau$.
--
--   This is what lets the analysis assume $\mathrm{MMS}=1$ and still speak about the unnormalized goal.
--
--   Differences from the source:
--   - generalization: v′(B) ≥ α implies v(B) ≥ αMMS → the equivalence v′(B) ≥ α ↔ v(B) ≥ αMMS; reason: the page's implication is one direction
--   - generalization: the normalized v′ used as a valuation of the analysis → explicit clauses that v′ is a valuation if v is and submodular if v is; reason: implicit in the page's use of v′; extra true conclusions, the page's clauses are all present
--   - encoding: the agent's safe strategy is unaffected → IsSafe at target τ·MMS for v ↔ IsSafe at target τ for v′, for every k and τ; reason: the page's sentence, with the target written on each scale
-- source:
--   Chawla, Huang, Kulkarni, Mehta, Shahkar, Single-or-Sample: Online Fair Allocation for Combinatorial Agents, STOC 2027 submission, arXiv:2609.32286 (manuscript sha256 28cd3d7b…), Appendix A, p.30

import Mathlib
import Definitions.Def_LittleCharity_MMS_Setting
import Definitions.Def_SubsamplingSM_Offline_IsSubmodular
import Definitions.Def_SingleOrSample_IsValuation
import Definitions.Def_SingleOrSample_IsSafe

namespace SingleOrSample

/-- **Appendix A, normalization** (Chawla, Huang, Kulkarni, Mehta, Shahkar, Single-or-Sample: Online Fair Allocation for Combinatorial Agents, STOC 2027 submission, arXiv:2609.32286 (manuscript sha256 28cd3d7b…), Appendix A, p.30). If `MMS v > 0` and `v' = v / MMS v`,
then `MMS v' = 1`; `v'(B) ≥ α` is equivalent to `v(B) ≥ α · MMS v`; the valuation and submodularity
properties pass over; rankings of sets and of marginal values are preserved; and the safe strategy at
target `τ` for `v'` is the safe strategy at target `τ · MMS v` for `v`.

**Formalization Note.** The page has "implies" for the second clause; the equivalence contains it. The
agent with `MMS v = 0` is the excluded case of footnote 3. -/
theorem appendix_A_normalization {m : ℕ} (n : ℕ) (v : Finset (Fin m) → ℝ)
    (hmms : 0 < LittleCharity.MMS.mms v n Finset.univ) :
    let M := LittleCharity.MMS.mms v n Finset.univ
    let v' : Finset (Fin m) → ℝ := fun S => M⁻¹ * v S
    LittleCharity.MMS.mms v' n Finset.univ = 1 ∧
    (∀ (B : Finset (Fin m)) (α : ℝ), α ≤ v' B ↔ α * M ≤ v B) ∧
    (IsValuation v → IsValuation v') ∧
    (SubsamplingSM.Offline.IsSubmodular v → SubsamplingSM.Offline.IsSubmodular v') ∧
    (∀ S T : Finset (Fin m), v' S ≤ v' T ↔ v S ≤ v T) ∧
    (∀ (A : Finset (Fin m)) (e f : Fin m),
      marginal v' A e ≤ marginal v' A f ↔ marginal v A e ≤ marginal v A f) ∧
    (∀ (k : ℕ) (τ : ℝ) (σ : Strategy m), IsSafe n k (τ * M) v σ ↔ IsSafe n k τ v' σ) := by sorry

end SingleOrSample
