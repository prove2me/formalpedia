-- Prove2me | Theorems.Thm_RunwayCPS_TotalDelay_proposition_3
-- name    : RunwayCPS.TotalDelay.proposition_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:11:22.955882+00:00
-- url     : https://prove2.me/theorems/df96703f-054b-4e1a-8fa9-e1d12d9fc991
-- title:
--   Proposition 3 — all source paths to a live node of the CPS network carry the same set of aircraft
-- statement:
--   Fix $n$ aircraft and a maximum position shift $k$, and consider the CPS network (without precedence pruning). Let $i$ be a node in stage $p$ that lies on at least one source-sink path. Then any two paths $v_1,\dots,v_p=i$ and $v'_1,\dots,v'_p=i$ from the source to $i$ contain the same set of aircraft before $i$:
--   $$\{\text{final aircraft of }v_1,\dots,v_{p-1}\}=\{\text{final aircraft of }v'_1,\dots,v'_{p-1}\}.$$
--
--   Consequently the partial objective $\theta_i(p-1)$ of §5.2 is computed over the same set of aircraft for every path reaching $i$, which is what the dynamic programming recursion of §5.2 relies on.
--
--   **Formalization Note** The paper states the proposition for every node of "the CPS network", which is the network after the removal of nodes unreachable from the source or from the sink (§3, p. 1653). The hypothesis that $i$ lies on a source-sink path makes this explicit. Without it the statement is false: for $n=5$, $k=1$, the stage-4 node $3$–$4$–$5$ is reached by $1\to1$–$3\to1$–$3$–$4$ and by $2\to2$–$3\to2$–$3$–$4$, with aircraft sets $\{1,3,4\}$ and $\{2,3,4\}$, and lies on no source-sink path. The statement is for the network without precedence pruning. Every path of the pruned network is a path of this network, so the statement covers the pruned one as well. Stages are 0-based (stage $s$ is the paper's stage $s+1$), and the aircraft of a node are read as its final aircraft (`List.getLast?`). The printed proof cites "Lemma 1" for the fact that a source-sink path has no repeated aircraft; that fact is Theorem 1.
-- source:
--   Balakrishnan & Chandran, Algorithms for Scheduling Runway Operations Under Constrained Position Shifting, Oper. Res. 58(6) (2010), p. 1656, Proposition 3 (with §3, p. 1653, removal of nodes not reachable from the source or the sink)

import Mathlib
import Definitions.Def_RunwayCPS_TotalDelay_Network

namespace RunwayCPS.TotalDelay

theorem proposition_3 {n : ℕ} (k s : ℕ) (i : List (Fin n)) (hs : s < n)
    (hlive : ∃ w : ℕ → List (Fin n), IsPath k w ∧ w s = i)
    (v v' : ℕ → List (Fin n)) (hv : IsPathTo k s i v) (hv' : IsPathTo k s i v') :
    {a : Fin n | ∃ q < s, (v q).getLast? = some a} =
      {a : Fin n | ∃ q < s, (v' q).getLast? = some a} := by sorry

end RunwayCPS.TotalDelay
