-- Prove2me | Theorems.Thm_SunGroupIso_Class2_theorem_1_1
-- name    : SunGroupIso.Class2.theorem_1_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T23:06:07.854977+00:00
-- url     : https://prove2.me/theorems/6613f5f7-79ab-4261-adc7-3fe3f1a6e5f9
-- title:
--   Theorem 1.1 — isomorphism of p-groups of class 2 in time N^{O((log N)^{25/26} log log N)}, for every prime p
-- statement:
--   There are one deterministic Turing machine $M$ and one constant $C$, fixed before the prime and the input, such that for every prime $p$, every $N$, all $p$-groups $G,H$ of nilpotency class 2 of order $N$ and all labellings of their elements by $0,\dots,N-1$, $M$ started on the code of the two Cayley tables halts within $\lceil N^{C(\log N)^{25/26}\log\log N}\rceil$ steps with output $1$ if $G\cong H$ and $0$ otherwise (natural logarithms; every such $N\ge p^3\ge8$, so $\log\log N>0$).
--
--   **Formalization Note** The machine is a Mathlib multi-stack Turing machine run through the published `HMBinPacking.OutputsWithin`; the input is the published code `GroupIsoPoly.encPair` of the two tables, of length $\Theta(N^2\log N)$.
--
--   Differences from the source:
--   - reading: 'there is an algorithm … in time p^{O(·)}' (the O-constant and the algorithm unspecified in their dependence on p) → one machine and one constant C chosen before the prime p and every other input; reason: the paper presents 'a general algorithm that works for all the possible p-groups of class 2' (p. 8, PDF p. 10); the uniform reading is the stronger one
--   - encoding: 'two p-groups … given by their Cayley tables' (§1, p. 1) → every labelling G ≃ Fin N, H ≃ Fin N of groups in Type, coded by encPair; one Mathlib TM2 machine through HMBinPacking.OutputsWithin; reason: any standard table code and machine model differ polynomially, and N^{O(·)} is closed under polynomials; every finite group is isomorphic to one in Type
--   - reading: 'can be decided' → the single output bit decide (Nonempty (G ≃* H)); reason: the standard meaning of a decision algorithm
--   - encoding: N^{O((log N)^{25/26} log log N)} → ⌈N^{C·(log N)^{25/26}·log log N}⌉ with natural logarithms and one natural C; reason: every input has N ≥ 8, where the exponent is positive, so one constant for all inputs is the O-unpacking and no threshold N₀ is needed
-- source:
--   Sun 2026, arXiv:2611.05920 (held version, sha256 22193308…), Theorem 1.1, p. 1 (PDF p. 3)

import Mathlib
import Definitions.Def_GroupIsoPoly_encPair
import Definitions.Def_HMBinPacking_OutputsWithin
import Definitions.Def_SunGroupIso_Class2_Basic

set_option autoImplicit false

open scoped Classical commutatorElement

namespace SunGroupIso.Class2

open ExponomialAssortment.FPTAS (encodeNat)
open GroupIsoPoly (encPair cayley)

/-- **Theorem 1.1** (Sun 2026, arXiv:2611.05920 (held version, sha256 22193308…), Theorem 1.1, p. 1, PDF p. 3): "For every prime p, isomorphism of two
p-groups of class 2 of order N can be decided in time N^{O((log N)^{25/26} log log N)}."

There are one deterministic multi-stack Turing machine `M` and one constant `C`, both fixed before the
prime, such that for every prime `p`, every `N`, all `p`-groups `G, H` of nilpotency class 2 and all
labellings `G ≃ Fin N`, `H ≃ Fin N`, `M` started on the code of the two Cayley tables halts within
`⌈N^(C·(log N)^(25/26)·log log N)⌉` steps with output `1` if `G ≅ H` and `0` otherwise. -/
theorem theorem_1_1 :
    ∃ M : Turing.TM2ComputableAux Bool Bool, ∃ C : ℕ,
      ∀ (p N : ℕ) (G H : Type) [Group G] [Group H] [Finite G] [Finite H]
        (eG : G ≃ Fin N) (eH : H ≃ Fin N),
        p.Prime → IsPGroupClass2 p G → IsPGroupClass2 p H →
        HMBinPacking.OutputsWithin M (encPair N (cayley eG) (cayley eH))
          [decide (Nonempty (G ≃* H))] (timeBound C N) := by sorry

end SunGroupIso.Class2
