-- Prove2me | Theorems.Thm_SymBoolPCSP_PolChar_pol_canonical_template_iff
-- name    : SymBoolPCSP.PolChar.pol_canonical_template_iff
-- status  : Proved
-- author  : @Alien60
-- created : 2026-11-05T19:24:17.785497+00:00
-- url     : https://prove2.me/theorems/ac70ef53-6f66-453a-aa22-aaa76ae4d0e2
-- title:
--   Polymorphisms of the canonical template are the functions whose $R$-ary minors lie in $S$
-- statement:
--   This is the canonical (long-code) promise template behind the Galois correspondence between polymorphism families and finite families of promise relations.
--
--   Let $D$ be a set, $R, L \ge 0$, and let $N = |D^R|$, with the coordinates $\{1,\dots,N\}$ identified with the tuples $y \in D^R$ through a fixed bijection $e$. Let $S$ be any set of functions $D^R \to D$. Consider the single promise relation $(P_R, Q_S)$ of arity $N$, where
--
--   1. $P_R = \{\, (y \mapsto y_j)_{y \in D^R} : j \in [R] \,\}$ consists of the $R$ dictator tuples, and
--   2. $Q_S = \{\, (y \mapsto g(y))_{y \in D^R} : g \in S \,\}$ consists of the value tables of the members of $S$.
--
--   Then for every $f : D^L \to D$,
--
--   $$
--   f \in \mathrm{Pol}(P_R, Q_S) \iff f^{\pi} \in S \ \text{ for every } \pi : [L] \to [R],
--   $$
--
--   where $f^{\pi}(y) = f(y_{\pi(1)}, \dots, y_{\pi(L)})$ is the projection (minor) of $f$ along $\pi$. No condition is placed on $S$, so $P_R \subseteq Q_S$ is not assumed.
--
--   The statement isolates the construction in the proof of Lemma 6.7 of Brakensiek–Guruswami: polymorphisms of the canonical template are exactly the functions all of whose $R$-ary minors lie in $S$. It can be reused for any Pippenger-type characterization of polymorphism families (promise or ordinary CSPs, e.g. Theorem 6.8 of the same paper) and wherever free structures or minion homomorphisms are described by minor conditions.
--
--   **Formalization Note** The signature has one relation symbol (`Unit`) of arity `N`; a tuple of the relation is a function `Fin N → D`, read through the bijection `e : Fin N ≃ (Fin R → D)`. `IsPolymorphism` and `projection` are the platform definitions from `PCSPBLPAff_Symmetric_Setting` and `SymBoolPCSP_PolChar_Basic`.
-- source:
--   J. Brakensiek, V. Guruswami, Promise Constraint Satisfaction: Algebraic Structure and a Symmetric Boolean Dichotomy, arXiv:1704.01937v2, §6.2, proof of Lemma 6.7, pp. 29–30

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting
import Definitions.Def_SymBoolPCSP_PolChar_Basic

namespace SymBoolPCSP.PolChar

open PCSPBLPAff.Symmetric

/-- The canonical ("long-code") promise template of arity `|D^R|`: coordinates are indexed by
`D^R` through `e`, the strong relation consists of the `R` dictator tuples `(y ↦ y_j)`, and the
weak relation consists of the graphs `(y ↦ g y)` of the functions `g ∈ S`. An `L`-ary `f` is a
polymorphism of this single promise relation iff every projection `f^π`, `π : [L] → [R]`,
lies in `S`. -/
theorem pol_canonical_template_iff {D : Type} {R N L : ℕ} (e : Fin N ≃ (Fin R → D))
    (S : Set ((Fin R → D) → D)) (f : (Fin L → D) → D) :
    IsPolymorphism
        (⟨fun _ => {t | ∃ j : Fin R, t = fun c => e c j}⟩ : RelStruct Unit (fun _ => N) D)
        (⟨fun _ => {t | ∃ g ∈ S, t = fun c => g (e c)}⟩ : RelStruct Unit (fun _ => N) D) f ↔
      ∀ π : Fin L → Fin R, projection f π ∈ S := by sorry

end SymBoolPCSP.PolChar
