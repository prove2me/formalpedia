-- Prove2me | Theorems.Thm_RamanujanLiftTower136_Tower_computing_generators
-- name    : RamanujanLiftTower136.Tower.computing_generators
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:44:51.729022+00:00
-- url     : https://prove2.me/theorems/b64fb94a-08d2-4b13-84c4-1c78d2c58be4
-- title:
--   Proposition 7.2 — computing and labeling all generators
-- statement:
--   For every admissible prime $p$, enumerate the box $|m_s|\le\lceil21p^{1/4}\rceil$ in the fixed integer basis, retain exactly the norm-$\pi$ solutions whose first nonzero coordinate is positive, and sort them lexicographically. The result contains exactly $p+1$ distinct representatives, one for each sign class in $S_p$. Conjugation and sign normalization locate the reverse-edge label $j^*$, which is an involution.
--
--   There are absolute $C,H>0$ and $k$ and a single finite-alphabet machine which, from binary $p$ and the selected $\pi$, outputs this list and its complete reverse-label table with
--   $$\operatorname{time}\le Cp^2(\lfloor\log_2p\rfloor+1)^k,\qquad \operatorname{bits}(x_j)\le H(\lfloor\log_2p\rfloor+1).$$
--   The uniqueness statement ranges over every norm-$\pi$ element of $E_0$, not only elements already in the search box. Thus it includes completeness of the enumeration.
--
--   Differences from the source:
--   - encoding: the fixed arithmetic objects and labeled graphs → the shared concrete definitions over the quadratic algebra, ZMod residues, and zero-based Fin label indices; reason: the representations preserve the field, orders, incidences, and all source instances
--   - reading: lexicographically first and lexicographically sorted integer coordinates → the usual signed-integer lexicographic order on pairs and eight-tuples; reason: the paper does not specify the order on signed coordinate vectors more explicitly
--   - reading: bit operations → steps of a finite-alphabet finite-control multi-stack machine with the stated binary encodings; reason: schoolbook arithmetic and bitwise Hensel lifting retain the cubic bound; fixed-prime lookup is absorbed only in its permitted constant
--   - encoding: O(p² poly(log p)) and O(log p) coefficient data → absolute C,k,H before p, a machine producing coordinates and reversal, and explicit length bounds for signed binary coordinates; reason: these give the source uniform bounds and preserve the exact search and label ordering
-- source:
--   Olga Kharlampovich, Igor Pak, Alina Vdovina, STOC 2027 submission #136 (October 2026), source.pdf SHA-256 27d691a82d8af863e511e7e6b00cee95779d914645846d2974f876836db8f83b, p.22 (PDF p.23), Proposition 7.2. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/136.pdf

import Definitions.Def_RamanujanLiftTower136_Tower_Ideals
import Definitions.Def_RamanujanLiftTower136_Tower_Computation

namespace RamanujanLiftTower136.Tower

theorem computing_generators :
  generatorsAlgorithm ∧ ∀ p : ℕ, admissible p → normalizedGenerators p := by sorry

end RamanujanLiftTower136.Tower
