-- Prove2me | Theorems.Thm_SkipFreeFluct_MBI_mbiQ_skipFree_QMatrix
-- name    : SkipFreeFluct.MBI.mbiQ_skipFree_QMatrix
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-10-29T10:46:27.484219+00:00
-- url     : https://prove2.me/theorems/126de8e7-b1cf-4722-bc94-b22f9c7e3d25
-- title:
--   The MBI Q-matrix (5.1) is a skip-free downward Q-matrix on $\{0,1,2,\dots\}$ (assumption (2.1))
-- statement:
--   Let $(\alpha,\mu,p,\beta,\nu,q)$ be MBI parameters: $\alpha>0$, $\mu$ a probability measure on $\{0,1,2,\dots\}$ with $\mu(0)>0$ and $\mu(1)=0$, $p,\beta,q\ge0$, and $\nu$ a probability measure on $\{1,2,\dots\}$. Let $Q$ be the matrix (5.1) on $E=\{0,1,2,\dots\}$:
--   $$Q(x,y)=\begin{cases}\mu(y-x+1)\,\alpha x+\nu(y-x)\,\beta,& y\ge x+1,\\ -(\alpha+p)x-(\beta+q),& y=x,\\ \mu(0)\,\alpha x,& y=x-1,\\ 0,& y\le x-2.\end{cases}$$
--   Then
--
--   1. $E$ is an integer interval with at least two points;
--   2. $Q$ is a Q-matrix on $E$: $Q(x,y)\ge0$ for $x\ne y$, each off-diagonal row is summable, and $\sum_{y\ne x}Q(x,y)\le -Q(x,x)$;
--   3. $Q$ satisfies the skip-free downward assumption (2.1): $Q(x,x-1)>0$ for $x\ge1$ and $Q(x,y)=0$ for $y\le x-2$.
--
--   This verifies that the MBI fits the general framework of Sections 2–3, so that the general fluctuation identities (Theorems 3.1 and 3.3) apply to it.
--
--   **Formalization Note** The three conclusions are `IsStateSpace`, `IsQMatrix` and `SkipFreeDown` for `mbiQ P` on `Set.Ici (0 : ℤ)`; the parameter constraints are `MBIParams.Valid`. Off-diagonal row sums equal $\alpha x(1-\mu(1))+\beta=\alpha x+\beta$, and the killing rate is $px+q\ge 0$.
-- source:
--   Loeffen, Patie, Wang, Fluctuation Theory of Continuous-Time, Skip-Free Downward Markov Chains with Applications to Branching Processes with Immigration, arXiv:2208.14425v1, §5, p. 12, Q-matrix (5.1), and §2, pp. 2–3, the Q-matrix definition and assumption (2.1)

import Mathlib
import Definitions.Def_SkipFreeFluct_MBI_Chain
import Definitions.Def_SkipFreeFluct_MBI_Model
open scoped ENNReal Topology
open Filter MeasureTheory

namespace SkipFreeFluct.MBI

theorem mbiQ_skipFree_QMatrix (P : MBIParams) (hP : P.Valid) :
    IsStateSpace (Set.Ici 0) ∧ IsQMatrix (Set.Ici 0) (mbiQ P) ∧
      SkipFreeDown (Set.Ici 0) (mbiQ P) := by sorry

end SkipFreeFluct.MBI
