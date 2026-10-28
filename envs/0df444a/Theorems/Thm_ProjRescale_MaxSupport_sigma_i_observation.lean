-- Prove2me | Theorems.Thm_ProjRescale_MaxSupport_sigma_i_observation
-- name    : ProjRescale.MaxSupport.sigma_i_observation
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T04:44:28.889845+00:00
-- url     : https://prove2.me/theorems/1aa7957e-926c-41b2-93f3-a9596b25e48c
-- title:
--   §2, p. 5 — σ_i observation: J(L) = {i : σ_i(L) > 0} and σ(L) = min_{i∈J(L)} σ_i(L)
-- statement:
--   Let $L \subseteq \mathbb R^n$ be a linear subspace and, for $i \in \{1,\dots,n\}$, let $\sigma_i(L) = \max\{x_i : x \in L \cap \mathbb R^n_+,\ \|x\|_\infty \le 1\}$. Then
--
--   $$J(L) = \{ i : \sigma_i(L) > 0 \} \qquad\text{and}\qquad \sigma(L) = \min_{i \in J(L)} \sigma_i(L)$$
--
--   (the second identity whenever $J(L) \neq \emptyset$, the case in which the minimum is defined).
--
--   So the vector $(\sigma_1(L),\dots,\sigma_n(L))$ encodes both $J(L)$ and $\sigma(L)$; the analysis of the rescaling step (Lemma 1) and of Algorithm 1 (Proposition 1) tracks these coordinates.
--
--   Differences from the source: none.
-- source:
--   Peña & Soheili, Projection and rescaling algorithm for finding maximum support solutions to polyhedral conic systems, arXiv:2003.08911v3, p. 5, §2 (unnumbered observation after the definition of σ_i(L))

import Mathlib
import Definitions.Def_ProjRescale_MaxSupport_Setting

namespace ProjRescale.MaxSupport

open Classical in
/-- §2, p. 5: `J(L) = {i : σ_i(L) > 0}` and `σ(L) = min_{i ∈ J(L)} σ_i(L)`. -/
theorem sigma_i_observation {n : ℕ} (L : Submodule ℝ (E n)) :
    maxSupp L = Finset.univ.filter (fun i => 0 < sigmaI L i) ∧
      ∀ h : (maxSupp L).Nonempty, condMeasure L = (maxSupp L).inf' h (sigmaI L) := by sorry

end ProjRescale.MaxSupport
