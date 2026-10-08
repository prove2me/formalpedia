-- Prove2me | Theorems.Thm_PrivateRelease_NetMechanism_observation_2_4
-- name    : PrivateRelease.NetMechanism.observation_2_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T16:10:02.39226+00:00
-- url     : https://prove2.me/theorems/5539e060-9a58-4022-b06c-032d0cc82249
-- title:
--   Observation 2.4 — a counting query has global sensitivity at most 1/n
-- statement:
--   Let $X$ be a data universe (any set), $n\ge 1$, and $\varphi:X\to\{0,1\}$ a predicate. The counting query $Q_\varphi(z)=\frac1n\#\{i: \varphi(z_i)=1\}$ on inputs $z\in X^n$ changes by at most $1/n$ when one entry of $z$ is replaced:
--   $$
--   GS_{Q_\varphi}\le\frac1n .
--   $$
--
--   This bound on the sensitivity of counting queries is what turns the general utility bound of the Net mechanism (Property 3.4) into its counting-query form (Corollary 3.5).
--
--   **Formalization Note** Neighbouring inputs differ in exactly one entry (`PrivLearn.Generic.Neighbors`). The input is read as the multiset of its entries. The global sensitivity is a real supremum over neighbouring pairs; the differences lie in $[0,1]$, so it is a genuine supremum for any $X$.
-- source:
--   Blum, Ligett, Roth, A Learning Theory Approach to Non-Interactive Database Privacy, arXiv:1109.2229v1 (2011), p. 6, Observation 2.4

import Mathlib
import Definitions.Def_PrivateRelease_NetMechanism_Queries

namespace PrivateRelease.NetMechanism

/-- Observation 2.4 (p. 6): for any predicate `φ : X → {0,1}`, the counting query
`Q_φ : Xⁿ → [0, 1]` has global sensitivity `GS_{Q_φ} ≤ 1/n` (replace-one neighbours). -/
theorem observation_2_4 {X : Type} (φ : X → Bool) (n : ℕ) (hn : 1 ≤ n) :
    GS (fun z : Fin n → X => countQ φ (inputDB z)) ≤ 1 / (n : ℝ) := by sorry

end PrivateRelease.NetMechanism
