-- Prove2me | Theorems.Thm_SymBoolPCSP_CFixing_par_minor_of_parity
-- name    : SymBoolPCSP.CFixing.par_minor_of_parity
-- status  : Proved
-- author  : @Alien60
-- created : 2026-11-06T18:24:27.41979+00:00
-- url     : https://prove2.me/theorems/924e8e1a-8e1d-4108-9fe5-3875f22ce076
-- title:
--   A folded function agreeing with parity on large subsets has Par_L₁ as a minor
-- statement:
--   Let $f : \{0,1\}^L \to \{0,1\}$ be folded with $f(0, \dots, 0) = 0$, let $L_1$ be odd, let $T \subseteq [L]$ and $C \in \mathbb{N}$. Suppose that
--
--   $$
--   f(e_X) = |X| \bmod 2 \quad \text{for every } X \subseteq T \text{ with } |X| \ge C,
--   $$
--
--   and that $|T| \ge L_1 (C + 1)$. Then $\mathrm{Par}_{L_1}$ is a minor of $f$: there is a map $\pi : [L] \to [L_1]$ with
--
--   $$
--   f(y_{\pi(1)}, \dots, y_{\pi(L)}) = \mathrm{Par}_{L_1}(y) \quad \text{for all } y \in \{0,1\}^{L_1}.
--   $$
-- source:
--   J. Brakensiek, V. Guruswami, Promise Constraint Satisfaction: Algebraic Structure and a Symmetric Boolean Dichotomy, arXiv:1704.01937v2, end of the proof of Lemma 4.10, p. 23

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting
import Definitions.Def_SymBoolPCSP_CFixing_Basic

open PCSPBLPAff.Symmetric
namespace SymBoolPCSP.CFixing

/-- Parity as a minor: let `f : {0,1}^L → {0,1}` be folded with `f(0,…,0) = 0`, let `L₁` be odd, `T ⊆ [L]` and `C ∈ ℕ`. If `f(e_X) = |X| mod 2` for every `X ⊆ T` with `|X| ≥ C`, and `|T| ≥ L₁(C + 1)`, then `Par_{L₁}` is a minor of `f`: there is `π : [L] → [L₁]` with `f(y_{π(1)}, …, y_{π(L)}) = Par_{L₁}(y)` for all `y ∈ {0,1}^{L₁}`. -/
theorem par_minor_of_parity {L L₁ : ℕ} (f : (Fin L → Bool) → Bool) (hfold : IsFolded f)
    (h0 : f (fun _ => false) = false) (hL₁ : Odd L₁) (T : Finset (Fin L)) (C : ℕ)
    (hpar : ∀ X ⊆ T, C ≤ X.card → f (indicator X) = decide (X.card % 2 = 1))
    (hT : L₁ * (C + 1) ≤ T.card) :
    ∃ π : Fin L → Fin L₁, ∀ y : Fin L₁ → Bool, f (fun i => y (π i)) = Par L₁ y := by sorry

end SymBoolPCSP.CFixing
