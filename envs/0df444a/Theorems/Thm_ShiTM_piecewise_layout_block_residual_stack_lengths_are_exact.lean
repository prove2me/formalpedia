-- Prove2me | Theorems.Thm_ShiTM_piecewise_layout_block_residual_stack_lengths_are_exact
-- name    : ShiTM.piecewise_layout_block_residual_stack_lengths_are_exact
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-18T08:21:37.964977+00:00
-- url     : https://prove2.me/theorems/63e3f1df-f51e-430c-bb27-7d5a31b8488b
-- title:
--   The piecewise layout block's residual stack lengths, exactly
-- statement:
--   The machine block that evaluates a piecewise-affine index map consumes its two piece-list stacks destructively and reports only that what remains is no longer than what it started with. That bound is enough to know the stacks must be restored, but not enough to price the restoration, which leaves any composition using the block with an inexact running time. Here the residual lengths are given exactly, as two recursions following the same relative-offset descent as the map itself: on the piece where the index is found, the length stack retains the unread remainder of that piece together with every later piece, while the base stack retains exactly the later pieces; on an advance both go whole and the descent continues. Two further hypotheses are needed and are shown to be necessary, since the block's own assumptions constrain only the non-empty case and leave the empty piece list free. The original bounds follow. Two indices lying in different pieces, found at different descent depths, are checked against the machine's literal residual lengths.

import Mathlib.Computability.TuringMachine.Computable
import Theorems.Thm_ShiTM_copy_loop_transfers_stack
import Theorems.Thm_ShiTM_branch_loop_transfers_prefix_until_symbol

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Turing Turing.TM2

namespace ShiTM

theorem piecewise_layout_block_residual_stack_lengths_are_exact :
    ∃ R1 R2 : List (ℕ × ℕ) → ℕ → ℕ,
    (∀ w : ℕ, R1 [] w = 0)
    ∧ (∀ (a b : ℕ) (t : List (ℕ × ℕ)) (w : ℕ),
        R1 ((a, b) :: t) w
          = if w < a then (a - w) + (t.map (fun p => p.1 + 1)).sum else R1 t (w - a))
    ∧ (∀ w : ℕ, R2 [] w = 0)
    ∧ (∀ (a b : ℕ) (t : List (ℕ × ℕ)) (w : ℕ),
        R2 ((a, b) :: t) w
          = if w < a then (t.map (fun p => p.2 + 1)).sum else R2 t (w - a))
    ∧
    (∀ {K : Type} [DecidableEq K] {Gam : K → Type} {Lam sig : Type}
    (M : Lam → Stmt Gam Lam sig) {kv kl kb kd ku kr : K}
    (hvl : kv ≠ kl) (hvb : kv ≠ kb) (hvd : kv ≠ kd) (hvu : kv ≠ ku) (hvr : kv ≠ kr)
    (hlb : kl ≠ kb) (hld : kl ≠ kd) (hlu : kl ≠ ku) (hlr : kl ≠ kr)
    (hbd : kb ≠ kd) (hbu : kb ≠ ku) (hbr : kb ≠ kr)
    (hdu : kd ≠ ku) (hdr : kd ≠ kr) (hur : ku ≠ kr)
    {l1 la la2 lf lo lend : Lam}
    {fL : sig → Option (Gam kl) → sig} {gL : sig → Bool}
    {fV : sig → Option (Gam kv) → sig} {gV : sig → Bool}
    {md : sig → Gam kd}
    {fD : sig → Option (Gam kd) → sig} {gD : sig → Bool} {hDp : sig → Gam kr}
    {fB : sig → Option (Gam kb) → sig} {gB : sig → Bool} {hPp : sig → Gam kr}
    {hQp : sig → Gam ku}
    {fO : sig → Option (Gam kd) → sig} {gO : sig → Bool} {hOp : sig → Gam ku}
    {eD : Gam kd → Gam kr} {eP : Gam kb → Gam kr}
    {eQ : Gam kb → Gam ku} {eO : Gam kd → Gam ku}
    (hM1 : M l1 = Stmt.pop kl fL (Stmt.branch gL
             (Stmt.pop kv fV (Stmt.branch gV
               (Stmt.push kd md (Stmt.goto (fun _ => l1)))
               (Stmt.goto (fun _ => lf))))
             (Stmt.goto (fun _ => la))))
    (hMa : M la = Stmt.pop kd fD (Stmt.branch gD
             (Stmt.push kr hDp (Stmt.goto (fun _ => la)))
             (Stmt.goto (fun _ => la2))))
    (hMa2 : M la2 = Stmt.pop kb fB (Stmt.branch gB
             (Stmt.push kr hPp (Stmt.goto (fun _ => la2)))
             (Stmt.goto (fun _ => l1))))
    (hMf : M lf = Stmt.pop kb fB (Stmt.branch gB
             (Stmt.push ku hQp (Stmt.goto (fun _ => lf)))
             (Stmt.goto (fun _ => lo))))
    (hMo : M lo = Stmt.pop kd fO (Stmt.branch gO
             (Stmt.push ku hOp (Stmt.goto (fun _ => lo)))
             (Stmt.goto (fun _ => lend))))
    {mv : Gam kv} {ml dl : Gam kl} {mb db : Gam kb} {mdc : Gam kd} {m : Gam ku}
    (hLm : ∀ w : sig, gL (fL w (some ml)) = true)
    (hLd : ∀ w : sig, gL (fL w (some dl)) = false)
    (hVs : ∀ (w : sig) (y : Gam kv), gV (fV w (some y)) = true)
    (hVn : ∀ w : sig, gV (fV w none) = false)
    (hmd : ∀ w : sig, md w = mdc)
    (hDs : ∀ (w : sig) (y : Gam kd), gD (fD w (some y)) = true)
    (hDn : ∀ w : sig, gD (fD w none) = false)
    (hDv : ∀ (w : sig) (y : Gam kd), hDp (fD w (some y)) = eD y)
    (hBm : ∀ w : sig, gB (fB w (some mb)) = true)
    (hBd : ∀ w : sig, gB (fB w (some db)) = false)
    (hPv : ∀ (w : sig) (y : Gam kb), hPp (fB w (some y)) = eP y)
    (hQv : ∀ (w : sig) (y : Gam kb), hQp (fB w (some y)) = eQ y)
    (hOs : ∀ (w : sig) (y : Gam kd), gO (fO w (some y)) = true)
    (hOn : ∀ w : sig, gO (fO w none) = false)
    (hOv : ∀ (w : sig) (y : Gam kd), hOp (fO w (some y)) = eO y)
    (hmQ : eQ mb = m) (hmO : eO mdc = m)
    (D C : List (ℕ × ℕ) → ℕ → ℕ)
    (hDc : ∀ (a b : ℕ) (t : List (ℕ × ℕ)) (w : ℕ),
      D ((a, b) :: t) w = if w < a then b + w else D t (w - a))
    (hCc : ∀ (a b : ℕ) (t : List (ℕ × ℕ)) (w : ℕ),
      C ((a, b) :: t) w = if w < a then 2 * w + b + 3 else 2 * a + b + 3 + C t (w - a))
    (PL : List (ℕ × ℕ) → List (Gam kl)) (PB : List (ℕ × ℕ) → List (Gam kb))
    (hPLc : ∀ (a b : ℕ) (t : List (ℕ × ℕ)),
      PL ((a, b) :: t) = List.replicate a ml ++ dl :: PL t)
    (hPBc : ∀ (a b : ℕ) (t : List (ℕ × ℕ)),
      PB ((a, b) :: t) = List.replicate b mb ++ db :: PB t)
    (hPL0 : PL ([] : List (ℕ × ℕ)) = [])
    (hPB0 : PB ([] : List (ℕ × ℕ)) = []),
    ∀ (ps : List (ℕ × ℕ)) (w : ℕ) (v : sig) (S : ∀ k, List (Gam k)),
      w < (ps.map Prod.fst).sum →
      S kv = List.replicate w mv → S kl = PL ps → S kb = PB ps → S kd = [] →
      ∃ (v' : sig) (T : ∀ k, List (Gam k)),
        (fun cf : Option (Cfg Gam Lam sig) => cf.bind (step M))^[C ps w]
            (some { l := some l1, var := v, stk := S })
          = some { l := some lend, var := v', stk := T }
        ∧ T ku = List.replicate (D ps w) m ++ S ku
        ∧ T kv = []
        ∧ T kd = []
        ∧ (T kl).length = R1 ps w
        ∧ (T kb).length = R2 ps w
        ∧ R1 ps w ≤ (PL ps).length
        ∧ R2 ps w ≤ (PB ps).length
        ∧ (T kl).length ≤ (S kl).length
        ∧ (T kb).length ≤ (S kb).length
        ∧ (∀ k, k ≠ kv → k ≠ kl → k ≠ kb → k ≠ kd → k ≠ ku → k ≠ kr → T k = S k))
    ∧ (∃ (Gam : Fin 6 → Type) (Lam sig : Type)
        (M : Lam → Turing.TM2.Stmt Gam Lam sig) (kv kl kb kd ku kr : Fin 6) (l1 lend : Lam)
        (mv : Gam kv) (ml dl : Gam kl) (mb db : Gam kb) (m : Gam ku)
        (PL : List (ℕ × ℕ) → List (Gam kl)) (PB : List (ℕ × ℕ) → List (Gam kb))
        (D C : List (ℕ × ℕ) → ℕ → ℕ)
        (v : sig) (S : ℕ → ∀ k, List (Gam k)) (pcs : List (ℕ × ℕ))
        (T4 T8 : ∀ k, List (Gam k)) (v4 v8 : sig),
        ([kv, kl, kb, kd, ku, kr] : List (Fin 6)).Nodup
        ∧ ml ≠ dl
        ∧ mb ≠ db
        ∧ (∀ (a b : ℕ) (t : List (ℕ × ℕ)),
            PL ((a, b) :: t) = List.replicate a ml ++ dl :: PL t)
        ∧ (∀ (a b : ℕ) (t : List (ℕ × ℕ)),
            PB ((a, b) :: t) = List.replicate b mb ++ db :: PB t)
        ∧ PL ([] : List (ℕ × ℕ)) = []
        ∧ PB ([] : List (ℕ × ℕ)) = []
        ∧ (∀ (a b : ℕ) (t : List (ℕ × ℕ)) (w : ℕ),
            D ((a, b) :: t) w = if w < a then b + w else D t (w - a))
        ∧ (∀ (a b : ℕ) (t : List (ℕ × ℕ)) (w : ℕ),
            C ((a, b) :: t) w
              = if w < a then 2 * w + b + 3 else 2 * a + b + 3 + C t (w - a))
        ∧ pcs = [(2, 0), (2, 2), (1, 2 + 3 * 2), (1, 2 + 3 * 2 + 1), (2, 2 + 3 * 2 + 1 + 1),
                 (2, 2 + 2), (1, 2 * 2 + 3 * 2 + 1 + 1), (1, 2 * 2 + 3 * 2 + 2 * 1 + 1),
                 (2, 2 * 2 + 3 * 2 + 2 * 1 + 2), (2, 2 + 2 * 2),
                 (1, 3 * 2 + 3 * 2 + 2 * 1 + 2), (1, 3 * 2 + 3 * 2 + 3 * 1 + 2),
                 (1, 3 * 2 + 3 * 2 + 3 * 1 + 3)]
        ∧ pcs.length = 13
        ∧ (PL pcs).length = 32
        ∧ (PB pcs).length = 142
        ∧ (∀ w : ℕ, S w kv = List.replicate w mv ∧ S w kl = PL pcs ∧ S w kb = PB pcs
            ∧ S w kd = [] ∧ S w ku = [])
        ∧ D pcs 4 = 8
        ∧ D pcs 8 = 4
        ∧ R1 pcs 4 = 25
        ∧ R2 pcs 4 = 129
        ∧ R1 pcs 8 = 18
        ∧ R2 pcs 8 = 103
        ∧ (fun cf : Option (Turing.TM2.Cfg Gam Lam sig) =>
            cf.bind (Turing.TM2.step M))^[C pcs 4]
            (some { l := some l1, var := v, stk := S 4 })
          = some { l := some lend, var := v4, stk := T4 }
        ∧ T4 ku = List.replicate 8 m
        ∧ (T4 kl).length = 25
        ∧ (T4 kb).length = 129
        ∧ (fun cf : Option (Turing.TM2.Cfg Gam Lam sig) =>
            cf.bind (Turing.TM2.step M))^[C pcs 8]
            (some { l := some l1, var := v, stk := S 8 })
          = some { l := some lend, var := v8, stk := T8 }
        ∧ T8 ku = List.replicate 4 m
        ∧ (T8 kl).length = 18
        ∧ (T8 kb).length = 103) := by
  sorry

end ShiTM
