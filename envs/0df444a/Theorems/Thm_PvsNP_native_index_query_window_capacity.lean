-- Prove2me | Theorems.Thm_PvsNP_native_index_query_window_capacity
-- name    : PvsNP.native_index_query_window_capacity
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-27T03:06:21.423345+00:00
-- url     : https://prove2.me/theorems/f6b9f88c-a319-4766-9a82-c27e00b7c5c2
-- title:
--   Index query time on native multitape machines with unrestricted work tapes
-- statement:
--   Suppose a preprocessed m-bit string can answer every index query after r native machine steps on k work tapes. For equal assignments the query starts with the same control and the same radius-r head-relative windows across indices. The input word, initial input head and output decoder may depend on the index. Absolute work head positions, tape contents outside the windows and prior output are unrestricted. Then 2^m is at most (|Q|+1) times (|Γ|+1) raised to k(2r+1). The decoder observes only output emitted during the query.
-- source:
--   Original formalization for the Prove2Me P vs NP mission using the mission library.

import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Run
import Mathlib

open Turing Turing.MultiTapeTM

theorem PvsNP.native_index_query_window_capacity {m k r : ℕ} {Γ Q : Type} [Fintype Γ] [Fintype Q]
    (tm : MultiTapeTM k Γ Q) (word : Fin m → List Γ)
    (start : (a : Fin m → Bool) → (j : Fin m) → Cfg k Γ Q (word j))
    (q : (Fin m → Bool) → Option Q)
    (w : (Fin m → Bool) → Fin k → Fin (2*r+1) → Option Γ)
    (pos : (j : Fin m) → Fin ((word j).length+2))
    (mode : ∀ a j, (start a j).state = q a)
    (position : ∀ a j, (start a j).inputPos = pos j)
    (cells : ∀ a j, (fun (i : Fin k) (v : Fin (2*r+1)) => (start a j).workTapes i
      ((start a j).workTapePos i + ((v.val : ℤ) - r))) = w a)
    (decode : Fin m → List Γ → Bool)
    (correct : ∀ a j, decode j (((tm.runFrom (start a j) r).output).drop (start a j).output.length) = a j) :
    2^m ≤ (Fintype.card Q + 1) * ((Fintype.card Γ + 1)^(2*r+1))^k := by sorry
