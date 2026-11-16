-- Prove2me | Theorems.Thm_PrivPACLower_ICP_Supplement_lemma_13
-- name    : PrivPACLower.ICP.Supplement.lemma_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:16:26.594202+00:00
-- url     : https://prove2.me/theorems/5cff7718-2cd6-4e35-ad24-94fffd6ca4dc
-- title:
--   Lemma 13 (used in the proof of Theorem 8) — dimensions and packings of paths and unions of paths
-- statement:
--   Let $k\ge1$ and $1\le d\le2^k$. There is a universal constant $c>0$ (uniform in $k$ and $d$) such that:
--
--   1. $\mathrm{VC}(\mathrm{Path}_k)=1$, $\mathrm{LDim}(\mathrm{Path}_k)=k$ and $ck\le\mathrm{PRDim}(\mathrm{Path}_k)\le k$;
--   2. $\mathrm{VC}(T_{d,k})=d$, $dk\le\mathrm{LDim}(T_{d,k})\le d(2k+1)$ and $c\,dk\le\mathrm{PRDim}(T_{d,k})\le d(2k+1)$;
--   3. $(\mathrm{Path}_k)^d\sqsubseteq T_{d,k}$, $\mathrm{Thr}_k\sqsubseteq\mathrm{Path}_k$ and $(\mathrm{Thr}_k)^d\sqsubseteq T_{d,k}$.
--
--   The paper writes $\Theta(k)$ and $\Theta(dk)$; the explicit upper bounds $k$ and $d(2k+1)$ and the lower bound $dk$ are those of its proof, and the lower constant $c$ comes from the Feldman–Xiao bound $\mathrm{PRDim}\ge c\cdot\mathrm{LDim}$. Paths have small VC dimension but large representation dimension, which is what makes packing them useful.
--
--   Differences from the source:
--   - encoding: Theta(k) and Theta(dk) → a universal lower constant c > 0 quantified before k and d, and the explicit upper bounds k, d(2k+1) and lower bound dk established in the proof; reason: the proof on p. 27 gives these explicit bounds; the Feldman–Xiao constant is universal
--   - encoding: VC dimension, Littlestone dimension (largest depth of a shattered complete mistake tree), probabilistic representation dimension → UnderstandingML.vcDim, UnderstandingML.ldim (published), and PRDim over PMFs on finite sets of hypotheses with log base 2; reason: same notions; on the finite domain X_k every distribution is a PMF; base 2 matches |Path_k| = 2^k in the proof
--   - encoding: the tree nodes X_k (binary strings of length <= k) with the prefix order; Thr_k packed into Path_k → TreeNodes k = lists of Booleans of length <= k with the list prefix relation; a one-entry tuple (Fin 1); reason: the same nodes and order; a single class is a 1-tuple in Definition 1
-- source:
--   Prathamesh Dharangutte, Amartya Sanyal, STOC 2027 submission #366 (October 2026), p. 27, Lemma 13 (proof p. 27). https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/366.pdf

import Mathlib
import Definitions.Def_PrivateUniformGen_Characterization_Privacy
import Definitions.Def_PrivPACLower_ICP_Learning
import Definitions.Def_PrivPACLower_ICP_Packing
import Definitions.Def_UnderstandingML_VC
import Definitions.Def_UnderstandingML_Online
import Definitions.Def_PrivPACLower_ICP_Supplement_Classes
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
set_option autoImplicit false

namespace PrivPACLower.ICP.Supplement

open PrivateUniformGen.Characterization PrivPACLower.ICP


theorem lemma_13 :
    ∃ c : ℝ, 0 < c ∧
      ∀ k d : ℕ, 1 ≤ k → 1 ≤ d → d ≤ 2 ^ k →
        (UnderstandingML.vcDim (Path k) = 1 ∧ UnderstandingML.ldim (Path k) = k ∧
          ENNReal.ofReal (c * k) ≤ PRDim (Path k) ∧ PRDim (Path k) ≤ k) ∧
        (UnderstandingML.vcDim (PathUnion d k) = d ∧
          ((d * k : ℕ) : ℕ∞) ≤ UnderstandingML.ldim (PathUnion d k) ∧
          UnderstandingML.ldim (PathUnion d k) ≤ ((d * (2 * k + 1) : ℕ) : ℕ∞) ∧
          ENNReal.ofReal (c * (d * k)) ≤ PRDim (PathUnion d k) ∧
          PRDim (PathUnion d k) ≤ ((d * (2 * k + 1) : ℕ) : ℝ≥0∞)) ∧
        (Packable (Y := fun _ : Fin d => TreeNodes k) (PathUnion d k) (fun _ => Path k) ∧
          Packable (Y := fun _ : Fin 1 => Fin k) (Path k) (fun _ => Thr k) ∧
          Packable (Y := fun _ : Fin d => Fin k) (PathUnion d k) (fun _ => Thr k)) := by sorry

end PrivPACLower.ICP.Supplement
