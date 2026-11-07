-- Prove2me | Theorems.Thm_SymBoolPCSP_CFixing_subset_true_of_relax_maj
-- name    : SymBoolPCSP.CFixing.subset_true_of_relax_maj
-- status  : Proved
-- author  : @Alien60
-- created : 2026-11-06T19:08:11.353794+00:00
-- url     : https://prove2.me/theorems/5972b99a-326a-429c-84ee-5deb75981a34
-- title:
--   m somewhere-increasing coordinates evaluate to 1 under (Ham_{2m+1}{m+1}, Ham_{2m+1}{0..2m})
-- statement:
--   Let $m \in \mathbb{N}$ and let $f : \{0,1\}^L \to \{0,1\}$ be a folded polymorphism of the promise relation $\big(\mathrm{Ham}_{2m+1}(\{m+1\}), \mathrm{Ham}_{2m+1}(\{0, \dots, 2m\})\big)$. Let $Z \subseteq [L]$ with $|Z| = m$ be such that every $j \in Z$ is somewhere-increasing for $f$: there is $Y \subseteq [L]$ with $j \notin Y$, $f(e_Y) = 0$ and $f(e_{Y \cup \{j\}}) = 1$. Then $f(e_Z) = 1$.
-- source:
--   J. Brakensiek, V. Guruswami, Promise Constraint Satisfaction: Algebraic Structure and a Symmetric Boolean Dichotomy, arXiv:1704.01937v2, proof of Lemma 4.12, Case 1, p. 24

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting
import Definitions.Def_SymBoolPCSP_CFixing_Basic

open PCSPBLPAff.Symmetric
namespace SymBoolPCSP.CFixing

/-- Case 1 of BG Lemma 4.12: let `f` be a folded polymorphism of
`(Ham_{2m+1}({m+1}), Ham_{2m+1}({0, …, 2m}))` and let `Z` be an `m`-set of coordinates on each
of which `f` is somewhere-increasing. Then `f(e_Z) = 1`. -/
theorem subset_true_of_relax_maj {L m : ℕ} (f : (Fin L → Bool) → Bool) (hfold : IsFolded f)
    (hpol : PolOf (Ham (2 * m + 1) {m + 1}) (Ham (2 * m + 1) (Set.Iic (2 * m))) f)
    (Z : Finset (Fin L)) (hZ : Z.card = m)
    (hwit : ∀ j ∈ Z, ∃ Y : Finset (Fin L), j ∉ Y ∧ f (indicator Y) = false ∧
      f (indicator (insert j Y)) = true) :
    f (indicator Z) = true := by sorry

end SymBoolPCSP.CFixing
