-- Prove2me | Theorems.Thm_StableDispatch_Markov_irreducible
-- name    : StableDispatch.Markov.irreducible
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:42:08.330856+00:00
-- url     : https://prove2.me/theorems/3512a358-d4e9-455a-83f1-f3ff4db3bc73
-- title:
--   Appendix A, p. 15 — the chain (Q(·), I(·)) on Zn+ × {1, …, n} is irreducible (and its rates form a conservative generator)
-- statement:
--   Fix $n$, $\lambda\in(0,1)$, a per-server message rate $\alpha_n>0$ and a rate vector $\mu\in\Sigma_n$, and let $Q$ be the generator of the chain $(Q(\cdot),I(\cdot))$ of the single-ID dispatching policy on $\mathbb Z_+^n\times\{1,\dots,n\}$. Then
--
--   1. $Q$ is a conservative generator: its off-diagonal entries are nonnegative and every row sums to $0$;
--   2. the chain is irreducible: for any two states $x,y$ there is a finite sequence $x=x_0,x_1,\dots,x_m=y$ of states with $x_{k}\ne x_{k+1}$ and
--   $$Q_{x_k,x_{k+1}}>0\qquad(0\le k<m).$$
--
--   Irreducibility is the first hypothesis of the Foster–Lyapunov criterion used to conclude Theorem 2.1; it also rules out absorbing states.
--
--   Differences from the source:
--   - encoding: the page states irreducibility only → the Lean statement adds the conjunct that the rates form a conservative generator (`IsGenerator`); reason: a well-formedness check of the encoded rates (Appendix A item 4 and the CTMC diagonal convention), true by construction and needed to read the matrix as a CTMC generator
--   - encoding: servers {1, …, n} → `Fin n` (0-based); reason: Lean convention, same instances
-- source:
--   Gamarnik, Tsitsiklis, Zubeldia, Stability, Memory, and Messaging Trade-Offs in Heterogeneous Service Systems, arXiv:2007.07219v1, p. 15, Appendix A, before (A.1)

import Mathlib
import Definitions.Def_MatrixAnalytic_Tree_Process
import Definitions.Def_StableDispatch_Markov_Setting

namespace StableDispatch.Markov

theorem irreducible (n : ℕ) (lam α : ℝ) (μ : Fin n → ℝ) (hlam0 : 0 < lam) (hlam1 : lam < 1)
    (hα : 0 < α) (hμ : μ ∈ Sigma n) :
    MatrixAnalytic.Tree.IsGenerator (gen n lam α μ) ∧
      MatrixAnalytic.Tree.IsIrreducibleGen (gen n lam α μ) := by sorry

end StableDispatch.Markov
