-- Prove2me | Theorems.Thm_SeymourThomas1993_haven_of_bramble
-- name    : SeymourThomas1993.haven_of_bramble
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-13T19:58:39.976976+00:00
-- url     : https://prove2.me/theorems/bfe404f0-6624-452b-a6e4-328da6ca1280
-- title:
--   Every finite bramble defines a haven of the same order
-- statement:
--   Every bramble of order at least k in a finite graph defines a haven of order k. For each vertex set W of size less than k, choose a connected component of G−W containing a bramble member missed by W. The selected components for any two such deletion sets touch. The theorem includes k=0 and empty vertex types.
-- source:
--   Dvorak and Norin, https://arxiv.org/pdf/1408.3869v2, Section 2.1, paragraph beginning Conversely following Theorem 2, PDF p. 3.

import Definitions.Def_SeymourThomas1993_Brambles
set_option autoImplicit false
open StableMSR.Recovery.Brambles StableMSR.Recovery.Havens

namespace SeymourThomas1993
theorem haven_of_bramble {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {family : Finset (Finset V)} {k : ℕ}
    (hB : IsBramble G family) (horder : OrderAtLeast family k) :
    ∃ β : Finset V → Finset V, Haven G k β := by sorry
end SeymourThomas1993
