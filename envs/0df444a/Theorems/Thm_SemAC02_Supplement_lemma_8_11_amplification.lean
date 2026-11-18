-- Prove2me | Theorems.Thm_SemAC02_Supplement_lemma_8_11_amplification
-- name    : SemAC02.Supplement.lemma_8_11_amplification
-- status  : Proved
-- author  : @Henry Yuen
-- created : 2026-11-17T20:02:13.329505+00:00
-- url     : https://prove2.me/theorems/c4ace191-522e-4977-a374-e86e7157eeca
-- title:
--   Lemma 8.11 — amplification by conjunction
-- statement:
--   Fix $d\ge2$. For all sufficiently small $\epsilon>0$ and every integer $t\ge1$, there is a monotone AND-rooted formula on some $m\ge1$ inputs, in the paper's normal form, of depth at most $d$ and tree size at most $t\exp(A\epsilon^{-1/(d-1)})$, where $A$ depends only on $d$, with acceptance probability at least $(4/5)^t$ under $\mathrm{Bern}(1/2)^m$ and at most $(1/5)^t$ under $\mathrm{Bern}(1/2-\epsilon)^m$.
--
--   This is Lemma 8.11 of the source, used between Lemmas 8.10 and 8.12. The asymptotic size constant is absorbed into the exponent constant $A$, chosen before $\epsilon$ and $t$. The explicit finite sum `bernProb` represents the product probability; `IsReduced` gives the source's normal-form convention; size is the number of tree nodes. The statement includes $m\ge1$ and retains an AND root.
-- source:
--   Alekseev, Gryaznov, Itsykson, Pitassi, Robere, Tzameret, Hard Instances for Strong Semantic Proof Systems: CNFs for Depth-Four PC and Deep Instances for AC0[2]-Frege, Lemma 8.11 (Amplification by conjunction), printed p.66, proof at p.67 in the public source https://www.doc.ic.ac.uk/~itzamere/Reslin_Simplification.pdf. The mission-pinned PDF has a different hash; the public source statement and proof have been checked.

import Mathlib
import Definitions.Def_SemAC02_Circ
import Definitions.Def_SemAC02_bernProb

namespace SemAC02.Supplement

theorem lemma_8_11_amplification (d : ℕ) (hd : 2 ≤ d) :
    ∃ A ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ t : ℕ, 1 ≤ t →
      ∃ m : ℕ, 1 ≤ m ∧ ∃ T : Circ (Fin m), IsMonotoneCirc T ∧ IsReduced T ∧
        (∃ cs, T = Circ.and cs) ∧ T.depth ≤ d ∧
        (T.treeSize : ℝ) ≤ (t : ℝ) * Real.exp (A * ε ^ (-1 / ((d : ℝ) - 1))) ∧
        (4 / 5 : ℝ) ^ t ≤ bernProb (1 / 2) (fun x => T.eval x) ∧
        bernProb (1 / 2 - ε) (fun x => T.eval x) ≤ (1 / 5 : ℝ) ^ t := by sorry

end SemAC02.Supplement
