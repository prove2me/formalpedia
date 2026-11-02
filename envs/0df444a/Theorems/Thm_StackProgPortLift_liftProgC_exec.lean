-- Prove2me | Theorems.Thm_StackProgPortLift_liftProgC_exec
-- name    : StackProgPortLift.liftProgC_exec
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-01T20:34:12.825822+00:00
-- url     : https://prove2.me/theorems/a3561a64-63e4-4e63-86b3-e8c8f93c9288
-- title:
--   Computable stack-port lifting preserves exact execution time
-- statement:
--   Let a structured stack program $P$ execute from local store $s$ to local store $t$ in exactly $n$ source steps. Let $r$ embed the local stack ports into a larger port set, and suppose an explicit decoder returns the unique local port exactly on the image of $r$. If a global store restricts along $r$ to $s$, then the computably lifted program executes in exactly $n$ steps and produces the global store obtained by replacing the selected ports with $t$.
--
--   All ports outside the image of $r$ retain their original contents. This compositional property lets independently verified parser, comparator, and gadget programs share one global store without changing their source-step bounds.
--
--   **Formalization Note** The decoder is part of the computable program construction; projection and write-back describe the input and output stores.
-- source:
--   Supporting stack-machine construction for the formalization of Agnetis, Mirchandani, Pacciarelli and Pacifici, Scheduling Problems with Two Competing Agents, Operations Research 52(2), 2004, Theorem 9.2, pp. 237–238. Port lifting and exact-step preservation are auxiliary formalization results, not claims from the paper.

import Mathlib
import Definitions.Def_StackProgPortLift

namespace StackProgPortLift

open CookPvsNP

theorem liftProgC_exec {K L A : Type} (r : K ↪ L) (decode : L → Option K)
    (hdecode : ∀ l k, decode l = some k ↔ r k = l)
    {p : StackProg K A} {s t : K → List A} {n : ℕ} (h : p.Exec s t n)
    (base : L → List A) (hb : project r base = s) :
    (liftProgC r decode p).Exec base (write r t base) n := by sorry

end StackProgPortLift
