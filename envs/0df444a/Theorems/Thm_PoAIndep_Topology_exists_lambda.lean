-- Prove2me | Theorems.Thm_PoAIndep_Topology_exists_lambda
-- name    : PoAIndep.Topology.exists_lambda
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T01:11:20.515299+00:00
-- url     : https://prove2.me/theorems/0bc5133f-9bc7-4a88-b677-47e19e5999ea
-- title:
--   §3.1, remark after Definition 3.2, p. 9 — ℓ*(0) = ℓ(0) ≤ ℓ(r) ≤ ℓ*(r), so some λ ∈ [0,1] solves ℓ*(λr) = ℓ(r)
-- statement:
--   Let $\ell$ be a standard latency function with marginal cost $\ell^*$, and let $r>0$. Then
--   $$\ell^*(0)=\ell(0)\le\ell(r)\le\ell^*(r),$$
--   and consequently there is $\lambda\in[0,1]$ with
--   $$\ell^*(\lambda r)=\ell(r).$$
--
--   This is the justification given after Definition 3.2 that the anarchy value is well defined: the scalar $\lambda$ exists because $\ell^*$ is continuous. The same scalars $\lambda_e$ define the scaled-down pseudoflow in Lemma 3.5 and Theorem 3.8.
--
--   **Formalization Note.** $\ell^*(0)$ is the one-sided derivative of $x\,\ell(x)$ at $0$.
-- source:
--   Roughgarden, The price of anarchy is independent of the network topology (journal-version manuscript, Dec. 23, 2002), p. 9, §3.1, paragraph after Definition 3.2

import Mathlib
import Definitions.Def_PoAIndep_Topology_Model

namespace PoAIndep.Topology

theorem exists_lambda (ℓ : ℝ → ℝ) (hℓ : IsStandard ℓ) (r : ℝ) (hr : 0 < r) :
    (marginalCost ℓ 0 = ℓ 0 ∧ ℓ 0 ≤ ℓ r ∧ ℓ r ≤ marginalCost ℓ r) ∧
      ∃ lam ∈ Set.Icc (0 : ℝ) 1, marginalCost ℓ (lam * r) = ℓ r := by sorry

end PoAIndep.Topology
