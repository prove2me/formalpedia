-- Prove2me | Theorems.Thm_ThomsonKS_Char_sigmaTilde_dense
-- name    : ThomsonKS.Char.sigmaTilde_dense
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:47:55.164978+00:00
-- url     : https://prove2.me/theorems/5562a289-00fb-49e6-aa01-a60f601e4d5b
-- title:
--   Proof of Theorem 3, p. 323 — every problem in Σ^P is a Hausdorff limit of problems in Σ̃^P
-- statement:
--   For every finite group $P$ of agents and every division problem $S \in \Sigma^P$ there is a sequence $(S^k)_{k \ge 0}$ of problems in $\tilde\Sigma^P$ converging to $S$ in the Hausdorff metric:
--
--   $$S^k \in \tilde\Sigma^P \ \text{for all } k, \qquad d_H(S^k, S) \to 0 .$$
--
--   Here $\tilde\Sigma^P$ is the class of problems of $\Sigma^P$ satisfying condition (c) (for all $x, y \in S$ with $y \geqslant x$ there is $z \in S$ with $z > x$). This density fact is the second ingredient of the proof of Theorem 3, alongside Theorem 2.
--
--   **Formalization Note** The Hausdorff distance is the extended Hausdorff distance for the sup metric on $\mathbb R^P$; groups are nonempty, as everywhere in the mission (see the Setting item).
-- source:
--   Thomson, The fair division of a fixed supply among a growing population, Math. Oper. Res. 8 (1983), p. 323, proof of Theorem 3 ('any element of Σ^P can be approximated by a sequence of elements of Σ̃^P')

import Mathlib
import Definitions.Def_ThomsonKS_Char_Setting

namespace ThomsonKS.Char

open Filter Topology

theorem sigmaTilde_dense : ∀ P : Finset ℕ, ∀ S ∈ DivProb P, ∃ Sk : ℕ → Set (P → ℝ),
    (∀ k, Sk k ∈ DivProbTilde P) ∧
      Tendsto (fun k => Metric.hausdorffEDist (Sk k) S) atTop (𝓝 0) := by sorry

end ThomsonKS.Char
