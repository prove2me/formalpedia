-- Prove2me | Theorems.Thm_TreeEdgeRankPC_am2cvp_p_complete
-- name    : TreeEdgeRankPC.am2cvp_p_complete
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:36:45.969464+00:00
-- url     : https://prove2.me/theorems/0c98488d-a968-480a-823f-7e340d739d17
-- title:
--   §3.2 — AM2CVP is P-complete under NC¹ reductions (cited: Greenlaw–Hoover–Ruzzo, Theorems 6.2.1, 6.2.3)
-- statement:
--   The Alternating Monotone Fanin 2, Fanout 2 Circuit Value Problem, with vertices given in topological order and the designated sink last, belongs to P, and every language in P reduces to it under NC¹ many-one reductions.
--
--   The paper cites this fact from the book of Greenlaw, Hoover and Ruzzo; in this mission it is a theorem to prove, never a hypothesis.
--
--   Differences from the source:
--   - reading: "uniform" family → logspace-uniform family; reason: p.12 defines only this uniformity; a weaker one would make the hardness claim weaker
--   - encoding: NC¹ computation of a polynomial-length string → `NC1Computable`, with (valid bit, data bit) output pairs, size ≤ n^k + k, depth ≤ c·⌊log₂ n⌋ + c, also a circuit for n = 0; reason: the standard padding convention for outputs of varying length; a constant-size circuit for the empty input changes nothing
--   - encoding: problems in P → languages over {0, 1}; P is the published `CookPvsNP.P Bool`; reason: the standard setting of [GHR95]; NC¹ circuits read bits
--   - encoding: an AM2CVP instance → the binary code `AM2Instance.enc`; a string that encodes no instance is not in the language; reason: a fixed injective encoding
-- source:
--   Giliberti–Hajiaghayi–Yun, Parallel Edge Ranking of Trees, arXiv:2610.12438 (held version of 2026-11-02, sha256 9e04ca7b…), §3.2, p.13 (AM2CVP P-complete, [GHR95, Thms 6.2.1, 6.2.3])

import Mathlib
import Definitions.Def_TreeEdgeRankPC_NC1
import Definitions.Def_TreeEdgeRankPC_AM2CVP

namespace TreeEdgeRankPC

/-- **AM2CVP is P-complete under NC¹ reductions**, §3.2, p.13, arXiv:2610.12438 (held version of 2026-11-02, sha256 9e04ca7b…), citing [GHR95, Theorems 6.2.1 and 6.2.3]: "We use
the Alternating Monotone Fanin 2, Fanout 2 CVP (AM2CVP), with binary AND and OR gates and fan-out at most two.
Every wire between gates joins opposite types, inputs feed only OR gates, and the designated output is an OR sink.
This restriction remains P-complete under NC^1 reductions with the vertices given in topological order."

**Formalization Note.** The paper cites this fact. Here it is a theorem to prove, not a hypothesis of anything:
membership in `CookPvsNP.P Bool` and hardness for every language in it. Vertices are in topological order with the
designated sink last, as `AM2Instance` requires. -/
theorem am2cvp_p_complete : PCompleteNC1 AM2CVP := by sorry

end TreeEdgeRankPC
