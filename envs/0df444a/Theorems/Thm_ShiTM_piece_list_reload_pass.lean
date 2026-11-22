-- Prove2me | Theorems.Thm_ShiTM_piece_list_reload_pass
-- name    : ShiTM.piece_list_reload_pass
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-17T23:20:12.967805+00:00
-- url     : https://prove2.me/theorems/e9217a5a-7886-40df-9d01-3162852099bc
-- title:
--   A reload pass that restores two consumed stacks from masters, with exact cost and frame
-- statement:
--   A RELOAD PASS for a six-stack Turing machine that re-establishes, from master copies, two working stacks that a previous block consumed. Setting: a block (the amplifier's piecewise wire-index layout block) requires its two piece-list stacks kl and kb to satisfy the EQUATIONS S kl = PL ps and S kb = PB ps, but guarantees on exit only the LENGTH BOUNDS (T kl).length <= (S kl).length and (T kb).length <= (S kb).length, having popped the piece-list material and discarded it. An element-iteration invariant can therefore neither drop those two clauses (they are the block's own precondition) nor keep them (a length bound is not an equation). This theorem supplies the missing pass. Master copies of the two lists sit, in reverse order and terminated by a sentinel symbol, on two further stacks kml and kmb; a shared scratch stack ks and a discard stack kd complete the six. For each working stack the pass runs four blocks: (i) a drain loop that empties the working stack into the discard stack, since push prepends and cannot overwrite; (ii) a counted transfer loop that pops the master until the sentinel, pushing each symbol to the working stack AND a mark to the scratch stack from ONE statement tree (one machine step per symbol, because stepAux recurses a whole statement tree inside one step); (iii) ONE step that re-pushes the sentinel onto the now-empty master, which is exactly what a packaged non-destructive copy cannot do, because its pass-1 exit arm is a bare goto and pop always consumes the symbol it tests; (iv) a drain of the scratch stack back onto the master, which restores the master bit-for-bit under the master list on top of the sentinel. The conclusion gives, for a starting state in ANY configuration of the working stacks: the exact step count (S kl).length + (S kb).length + 2*(pa.length + pb.length) + 8; the two restored equations T kl = PL ps and T kb = PB ps; both masters intact, T kml = S kml and T kmb = S kmb; the scratch drained, T ks = []; an explicit FRAME CONDITION naming the six touched stacks; a higher-order transparency clause, for all P, (for all A B, frame -> P A -> P B) -> P S -> P T, so a consumer instantiates P with its own iteration invariant and needs no bridging lemma; a Nonempty EvalsToInTime witness at the exact count; the length identities (PL ps).length = pa.length and (PB ps).length = pb.length; and the closed bound 3*((PL ps).length + (PB ps).length) + 8 on the cost whenever the incoming junk is bounded by the piece lists, as the consuming block guarantees. A second, unconditional conjunct is a NON-VACUITY witness: one concrete six-stack machine over the alphabet Option Bool, run from a NON-TRIVIAL start in which the working stacks are genuinely SHORTER than their targets (2 symbols against 5, and 1 against 6), for the two-piece list [(2,1),(1,3)] whose pieces have different lengths, halting in exactly 33 steps with both working stacks correct, both masters intact and the scratch empty.

import Mathlib.Computability.TuringMachine.Computable
import Theorems.Thm_ShiTM_counted_loop_transfers_prefix_with_marks
import Theorems.Thm_ShiTM_copy_loop_transfers_stack

set_option autoImplicit false

namespace ShiTM

open Turing Turing.TM2

theorem piece_list_reload_pass :
    (∀
    {K : Type} [DecidableEq K] {Gam : K → Type} {Lam sig : Type}
    (M : Lam → Stmt Gam Lam sig) {kl kb kml kmb ks kd : K}
    (h01 : kl ≠ kb) (h02 : kl ≠ kml) (h03 : kl ≠ kmb) (h04 : kl ≠ ks) (h05 : kl ≠ kd)
    (h12 : kb ≠ kml) (h13 : kb ≠ kmb) (h14 : kb ≠ ks) (h15 : kb ≠ kd)
    (h23 : kml ≠ kmb) (h24 : kml ≠ ks) (h25 : kml ≠ kd)
    (h34 : kmb ≠ ks) (h35 : kmb ≠ kd) (h45 : ks ≠ kd)
    {ldr1 la1 lx1 lp1 ldr2 la2 lx2 lp2 lnd : Lam}
    {fDa : sig → Option (Gam kl) → sig} {gDa : sig → Bool} {hDa : sig → Gam kd}
    {f1a : sig → Option (Gam kml) → sig} {g1a : sig → Bool}
    {h1a : sig → Gam kl} {hma : sig → Gam ks} {fca : sig → Gam kml}
    {f2a : sig → Option (Gam ks) → sig} {g2a : sig → Bool} {h2a : sig → Gam kml}
    {fDb : sig → Option (Gam kb) → sig} {gDb : sig → Bool} {hDb : sig → Gam kd}
    {f1b : sig → Option (Gam kmb) → sig} {g1b : sig → Bool}
    {h1b : sig → Gam kb} {hmb : sig → Gam ks} {fcb : sig → Gam kmb}
    {f2b : sig → Option (Gam ks) → sig} {g2b : sig → Bool} {h2b : sig → Gam kmb}
    (eDa : Gam kl → Gam kd) (e1a : Gam kml → Gam kl) (mka : Gam kml → Gam ks)
    (e2a : Gam ks → Gam kml)
    (eDb : Gam kb → Gam kd) (e1b : Gam kmb → Gam kb) (mkb : Gam kmb → Gam ks)
    (e2b : Gam ks → Gam kmb)
    (hMda : M ldr1 = Stmt.pop kl fDa (Stmt.branch gDa
              (Stmt.push kd hDa (Stmt.goto (fun _ => ldr1)))
              (Stmt.goto (fun _ => la1))))
    (hMaa : M la1 = Stmt.pop kml f1a (Stmt.branch g1a
              (Stmt.push kl h1a (Stmt.push ks hma (Stmt.goto (fun _ => la1))))
              (Stmt.goto (fun _ => lx1))))
    (hMxa : M lx1 = Stmt.push kml fca (Stmt.goto (fun _ => lp1)))
    (hMpa : M lp1 = Stmt.pop ks f2a (Stmt.branch g2a
              (Stmt.push kml h2a (Stmt.goto (fun _ => lp1)))
              (Stmt.goto (fun _ => ldr2))))
    (hMdb : M ldr2 = Stmt.pop kb fDb (Stmt.branch gDb
              (Stmt.push kd hDb (Stmt.goto (fun _ => ldr2)))
              (Stmt.goto (fun _ => la2))))
    (hMab : M la2 = Stmt.pop kmb f1b (Stmt.branch g1b
              (Stmt.push kb h1b (Stmt.push ks hmb (Stmt.goto (fun _ => la2))))
              (Stmt.goto (fun _ => lx2))))
    (hMxb : M lx2 = Stmt.push kmb fcb (Stmt.goto (fun _ => lp2)))
    (hMpb : M lp2 = Stmt.pop ks f2b (Stmt.branch g2b
              (Stmt.push kmb h2b (Stmt.goto (fun _ => lp2)))
              (Stmt.goto (fun _ => lnd))))
    (hDca : ∀ (w : sig) (y : Gam kl), gDa (fDa w (some y)) = true)
    (hDna : ∀ w : sig, gDa (fDa w none) = false)
    (hDva : ∀ (w : sig) (y : Gam kl), hDa (fDa w (some y)) = eDa y)
    (h1va : ∀ (w : sig) (y : Gam kml), h1a (f1a w (some y)) = e1a y)
    (hmva : ∀ (w : sig) (y : Gam kml), hma (f1a w (some y)) = mka y)
    (h2ca : ∀ (w : sig) (z : Gam ks), g2a (f2a w (some z)) = true)
    (h2na : ∀ w : sig, g2a (f2a w none) = false)
    (h2va : ∀ (w : sig) (z : Gam ks), h2a (f2a w (some z)) = e2a z)
    (hinva : ∀ y : Gam kml, e2a (mka y) = y)
    (hDcb : ∀ (w : sig) (y : Gam kb), gDb (fDb w (some y)) = true)
    (hDnb : ∀ w : sig, gDb (fDb w none) = false)
    (hDvb : ∀ (w : sig) (y : Gam kb), hDb (fDb w (some y)) = eDb y)
    (h1vb : ∀ (w : sig) (y : Gam kmb), h1b (f1b w (some y)) = e1b y)
    (hmvb : ∀ (w : sig) (y : Gam kmb), hmb (f1b w (some y)) = mkb y)
    (h2cb : ∀ (w : sig) (z : Gam ks), g2b (f2b w (some z)) = true)
    (h2nb : ∀ w : sig, g2b (f2b w none) = false)
    (h2vb : ∀ (w : sig) (z : Gam ks), h2b (f2b w (some z)) = e2b z)
    (hinvb : ∀ y : Gam kmb, e2b (mkb y) = y)
    (cma : Gam kml) (hfca : ∀ w : sig, fca w = cma)
    (cmb : Gam kmb) (hfcb : ∀ w : sig, fcb w = cmb)
    (pa ta : List (Gam kml))
    (h1ca : ∀ (w : sig) (y : Gam kml), y ∈ pa → g1a (f1a w (some y)) = true)
    (hstpa : ∀ w : sig, g1a (f1a w (some cma)) = false)
    (pb tb : List (Gam kmb))
    (h1cb : ∀ (w : sig) (y : Gam kmb), y ∈ pb → g1b (f1b w (some y)) = true)
    (hstpb : ∀ w : sig, g1b (f1b w (some cmb)) = false)
    (PL : List (ℕ × ℕ) → List (Gam kl)) (PB : List (ℕ × ℕ) → List (Gam kb))
    (ps : List (ℕ × ℕ))
    (hpla : (List.map e1a pa).reverse = PL ps)
    (hplb : (List.map e1b pb).reverse = PB ps)
    (v : sig) (S : ∀ k, List (Gam k))
    (hSma : S kml = pa ++ cma :: ta) (hSmb : S kmb = pb ++ cmb :: tb)
    (hSs : S ks = []),
    ∃ (v' : sig) (T : ∀ k, List (Gam k)),
      (fun cf : Option (Cfg Gam Lam sig) => cf.bind (step M))^[(S kl).length
          + (S kb).length + 2 * (pa.length + pb.length) + 8]
          (some { l := some ldr1, var := v, stk := S })
        = some { l := some lnd, var := v', stk := T }
      ∧ T kl = PL ps
      ∧ T kb = PB ps
      ∧ T kml = S kml
      ∧ T kmb = S kmb
      ∧ T ks = []
      ∧ (∀ k, k ≠ kl → k ≠ kb → k ≠ kml → k ≠ kmb → k ≠ ks → k ≠ kd → T k = S k)
      ∧ (∀ P : (∀ k, List (Gam k)) → Prop,
          (∀ A B : (∀ k, List (Gam k)),
            (∀ k, k ≠ kl → k ≠ kb → k ≠ kml → k ≠ kmb → k ≠ ks → k ≠ kd → A k = B k) →
              P A → P B) →
            P S → P T)
      ∧ Nonempty (StateTransition.EvalsToInTime (step M)
          { l := some ldr1, var := v, stk := S }
          (some { l := some lnd, var := v', stk := T })
          ((S kl).length + (S kb).length + 2 * (pa.length + pb.length) + 8))
      ∧ (PL ps).length = pa.length
      ∧ (PB ps).length = pb.length
      ∧ ((S kl).length ≤ (PL ps).length → (S kb).length ≤ (PB ps).length →
          (S kl).length + (S kb).length + 2 * (pa.length + pb.length) + 8
            ≤ 3 * ((PL ps).length + (PB ps).length) + 8)
    )
    ∧
    ∃ (Gm : Fin 6 → Type) (Lm sg : Type) (Mw : Lm → Stmt Gm Lm sg)
      (kl kb kml kmb ks kd : Fin 6) (lst lfn : Lm)
      (Sw Tw : ∀ k, List (Gm k)) (u0 u1 : sg)
      (LL : List (Gm kl)) (BB : List (Gm kb)),
      ([kl, kb, kml, kmb, ks, kd] : List (Fin 6)).Nodup
      ∧ lst ≠ lfn
      ∧ LL.length = 5
      ∧ BB.length = 6
      ∧ (Sw kl).length = 2
      ∧ (Sw kb).length = 1
      ∧ (Sw kl).length < LL.length
      ∧ (Sw kb).length < BB.length
      ∧ Sw kl ≠ LL
      ∧ Sw kb ≠ BB
      ∧ Sw ks = []
      ∧ Sw kml ≠ []
      ∧ Sw kmb ≠ []
      ∧ (fun cf : Option (Cfg Gm Lm sg) => cf.bind (step Mw))^[33]
          (some { l := some lst, var := u0, stk := Sw })
        = some { l := some lfn, var := u1, stk := Tw }
      ∧ Tw kl = LL
      ∧ Tw kb = BB
      ∧ Tw kml = Sw kml
      ∧ Tw kmb = Sw kmb
      ∧ Tw ks = []
      ∧ Nonempty (StateTransition.EvalsToInTime (step Mw)
          { l := some lst, var := u0, stk := Sw }
          (some { l := some lfn, var := u1, stk := Tw }) 33) := by
  sorry

end ShiTM
