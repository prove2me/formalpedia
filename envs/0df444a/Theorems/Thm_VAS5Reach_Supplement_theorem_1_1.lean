-- Prove2me | Theorems.Thm_VAS5Reach_Supplement_theorem_1_1
-- name    : VAS5Reach.Supplement.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:49:57.69762+00:00
-- url     : https://prove2.me/theorems/b52e40b0-292f-4050-b3e3-c4edbcc2dcef
-- title:
--   Theorem 1.1 — 5-VAS reachability is PSPACE-complete under binary and NL-complete under unary encoding
-- statement:
--   The reachability problem for 5-VAS — given a finite set $T\subseteq\mathbb Z^5$ and $s,t\in\mathbb N^5$, decide whether $s\xrightarrow{*}t$ — is
--
--   1. in PSPACE under binary encoding;
--   2. PSPACE-hard under binary encoding;
--   3. in NL under unary encoding;
--   4. NL-hard under unary encoding,
--
--   where hardness is under log-space many-one reductions. That is, 5-VAS reachability is PSPACE-complete under binary encoding and NL-complete under unary encoding.
--
--   This settles the complexity of 5-VAS reachability and matches the bounds known for 2-VASS. The two hardness halves are cited by the paper from [CFZ26, Theorem 1.2] and [KL27, Theorem 1]; the upper bounds follow from the polynomial reachability distance of Theorem 1.2.
--
--   **Formalization Note** The two problems are the languages `reachLangBin 5` and `reachLangUnary 5`; all classes are taken in the published `SpaceMachine` model.
--
--   Differences from the source:
--   - reading: PSPACE-complete / NL-complete (the kind of reduction is not named) → hardness under log-space many-one reductions (HardFor … LogspaceComputable) for both claims; reason: the standard reduction for NL-completeness (under polynomial-time reductions every nontrivial language in NL would be NL-hard), and the convention of the matching 2-VASS result [BEF+21]; it is the stronger of the two readings for PSPACE
--   - encoding: binary encoding of a 5-VAS instance (V, s, t) → the language reachLangBin 5: words that are the code of some (L, s, t) with s −∗→ t in the VAS L.toFinset; transitions listed as a list L (repeats allowed), each number a self-delimiting field (pairs 0b per bit, separator 10), integers as sign bit + binary digits of |z|; reason: any standard binary code; its length is polynomially related to SIZE_BIN (p.44), and the classes are closed under the log-space conversions between such codes; non-codes are not in the language
--   - encoding: unary encoding of a 5-VAS instance (V, s, t) → the language reachLangUnary 5: the same fields with every integer z written as a sign bit and |z| ones; reason: the length of the code is polynomially related to SIZE(V, s, t) (p.14); same remarks as for the binary code
--   - encoding: PSPACE, NL and log-space many-one reductions (Turing machines) → the published SpaceMachine model (multitape, read-only input, write-only output, space = visited work cells): published InNL (machines halting on every branch on every input, work space ≤ c·log₂(n+2)), published LogspaceComputable and HardFor, and InPSPACE = a deterministic machine halting on every input with work space ≤ p(n) for a polynomial p; reason: standard models; a logarithmic or polynomial space machine can be given a clock, so requiring every branch to halt does not change NL or PSPACE
-- source:
--   Chen, Fu, Fu, Reachability in Five-Dimensional Vector Addition Systems Is PSPACE-Complete, arXiv:2610.40012 (held version, sha256 a74d76f9…), Theorem 1.1, p.2 (PDF p.4); restated and proved App. A.1, p.44 (PDF p.46); hardness cited from [CFZ26, Theorem 1.2] and [KL27, Theorem 1]

import Mathlib
import Definitions.Def_VAS5Reach_Supplement_reachLang
import Definitions.Def_VAS5Reach_Supplement_InPSPACE

namespace VAS5Reach.Supplement

/-- **Theorem 1.1.** The reachability problem for 5-VAS is PSPACE-complete under binary encoding
and NL-complete under unary encoding.

Source: W. Chen, B. Fu, Y. Fu, *Reachability in Five-Dimensional Vector Addition Systems Is
PSPACE-Complete*, arXiv:2610.40012 (held version, sha256 a74d76f9…), Theorem 1.1, printed p. 2
(PDF p. 4); restated and proved in App. A.1, printed p. 44 (PDF p. 46). The NL-hardness and the
PSPACE-hardness are cited from [CFZ26, Theorem 1.2] and [KL27, Theorem 1]; the proofs are not in
this paper.

All four parts are stated: binary 5-VAS reachability is in PSPACE and PSPACE-hard; unary 5-VAS
reachability is in NL and NL-hard.

**Formalization Note** Languages over `{0,1}` (`reachLangBin 5`, `reachLangUnary 5`); PSPACE, NL
and log-space computability are in one machine model (the published
`ArrighiStarFree.HalfLevel.SpaceMachine`, with the published `InNL`, `LogspaceComputable`,
`HardFor`); hardness is under log-space many-one reductions. -/
theorem theorem_1_1 :
    PSPACECompleteLog (reachLangBin 5) ∧ NLCompleteLog (reachLangUnary 5) := by sorry

end VAS5Reach.Supplement
