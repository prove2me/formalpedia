-- Prove2me | Theorems.Thm_TimeSpaceMA_widthListComputable_to_coinFreeRAM
-- name    : TimeSpaceMA.widthListComputable_to_coinFreeRAM
-- status  : Proved
-- author  : @bersubs
-- created : 2026-11-14T19:40:42.112922+00:00
-- url     : https://prove2.me/theorems/c223959d-82be-4fb4-9f81-42406c591443
-- title:
--   Polynomial log-cost RAM simulation of a binary list computation
-- statement:
--   Let a deterministic polynomial-time multitape machine compute a finite list of naturals from a triple $(n,k,v)$ using a unary width $n$ and binary values for the other two fields. Then there is one coin-free log-cost RAM program $P$ and an exponent $e$ such that for every $n\ge1$, $k\le n$, and $v<2^n$, starting $P$ with $[n,k,v]$ in memory halts with work at most $n^e+e$. At halt cell zero holds the list length and consecutive cells from address one hold the list entries.
--
--   This is the reverse machine-model transfer and output convention needed for a uniform neighbor listing. The unary width lets the source computation take polynomial time in $n$ even for small numerical labels.
-- source:
--   Cook and Reckhow, Time Bounded Random Access Machines, JCSS 7 (1973), Theorem 2(b), https://www.cs.toronto.edu/~sacook/homepage/rams.pdf. Adapted to the published log-cost RAM, finite binary list I/O, and the polynomial bound in the width.

import Definitions.Def_TimeSpaceMA_RAM
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_PolyTime
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_List
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Nat
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Pair
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Unary

namespace TimeSpaceMA

open Turing.MultiTapeTM

/-- Compile a polynomial-time binary list computation to the log-cost RAM's length and
consecutive-record output convention. The width is provided in unary to the source machine. Only valid width, entropy, and vertex triples need
be simulated within the width-based polynomial cost bound. -/
theorem widthListComputable_to_coinFreeRAM
    (listing : ℕ × ℕ × ℕ → List ℕ)
    (hlisting : ComputableInPolyTime listing (encPair encUnary (encPair encNat encNat))
      (encList encNat)) :
    ∃ (e : ℕ) (P : Program), P.CoinFree ∧
      ∀ n k v : ℕ, 1 ≤ n → k ≤ n → v < 2^n →
        ∃ st, P.RunsTo zeroTape (memOf [n,k,v]) st ∧ st.work ≤ n^e+e ∧
          st.mem 0 = (listing (n,k,v)).length ∧
          ∀ i : Fin (listing (n,k,v)).length, st.mem (1+i.val) = (listing (n,k,v))[i] := by sorry

end TimeSpaceMA
