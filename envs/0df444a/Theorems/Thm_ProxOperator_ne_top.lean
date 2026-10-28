-- Prove2me | Theorems.Thm_ProxOperator_ne_top
-- name    : ProxOperator.ne_top
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-27T04:18:40.589012+00:00
-- url     : https://prove2.me/theorems/d8292617-d8d3-4b0f-a515-961b04c79f42
-- title:
--   A proximal point lies in the domain of the function
-- statement:
--   Let $H$ be a real inner product space, let $f : H \to \overline{\mathbb{R}}$ be proper,
--   closed and convex, and let $P$ be the proximal operator of $f$ at parameter $\gamma$, so that
--   $P x$ is the minimizer of $y \mapsto f(y) + \tfrac{1}{2\gamma}\|y - x\|^2$. Then for every
--   $x \in H$
--
--   $$
--   f(P x) \;\neq\; +\infty ,
--   $$
--
--   that is, $P x$ lies in the effective domain of $f$.
--
--   A proximal step never leaves the domain. The statement looks like bookkeeping and is used as a
--   side condition everywhere: as soon as a proof wants to compute with $f(Px)$ as a real number --
--   to subtract it, to bound it, to put it in an inequality -- it needs exactly this, and an
--   $\overline{\mathbb{R}}$-valued convex analysis offers no way around it.
--
--   **Formalization Note** Properness, closedness and convexity are the platform definition
--   `IsProperClosedConvex`, and `IsProx γ f P` says that `P` is the proximal operator; both come
--   from the imported definition modules.
-- source:
--   R. T. Rockafellar, Convex Analysis, Princeton 1970, §23. Carved from the accepted proof of NesterovFB.Weak.theorem_3 (the rate of convergence of Nesterov’s accelerated forward-backward method), https://prove2.me/submissions/e3454a9c-3502-4c6b-9794-7eebefc4332c

import Mathlib
import Definitions.Def_ThreeOpSplitting_ConvexRates_Problem
import Definitions.Def_ThreeOpSplitting_Convergence_WeakConvergence
import Definitions.Def_NesterovFB_Weak_Algorithm

open Filter Topology NNReal
open InnerProductSpace
open ThreeOpSplitting.ConvexRates

theorem ProxOperator.ne_top {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (γ : ℝ) (f : H → EReal) (P : H → H) (hf : IsProperClosedConvex f) (hP : IsProx γ f P)
    (x : H) : f (P x) ≠ ⊤ := by sorry
