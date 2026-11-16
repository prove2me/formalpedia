-- Prove2me | Theorems.Thm_RobustBoolPCSP_Supplement_theorem_5_20
-- name    : RobustBoolPCSP.Supplement.theorem_5_20
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T01:34:27.682974+00:00
-- url     : https://prove2.me/theorems/7d346e9c-3dcc-4ba2-960a-99f21ea294a8
-- title:
--   Theorem 5.20 (A majority condition forced by mode certificates) — $h\circ d$, $h$ satisfy $\Sigma_{\mathrm{maj}}$; $\mathrm{PP}(\mathrm{MC})\models\Sigma_{\mathrm{maj}}$
-- statement:
--   Let $T$ be a template whose pulled-back pairs $(P_j,W_j)$ all have the mode property for the output map $h$, and let $d(x,y,z)=y$ if $y=z$ and $d(x,y,z)=x$ otherwise. Then $f=h\circ d$ and $u=h$ are polymorphisms of $T$ and satisfy
--
--   $$\Sigma_{\mathrm{maj}}:\quad f(x,x,y)=f(x,y,x)=f(y,x,x)=u(x).$$
--
--   Consequently every template in $\mathrm{PP}(\mathrm{MC})$ satisfies $\Sigma_{\mathrm{maj}}$.
--
--   The condition gives an obstruction to membership in $\mathrm{PP}(\mathrm{MC})$ that is invariant under pp-constructions.
--
--   Differences from the source:
--   - encoding: PP(MC), pp-constructibility in the sense of [BBKO21] → finite chains of pp-powers (n ≥ 1, finite signature, equality atoms allowed) and homomorphic relaxations, all templates finite with nonempty domains; reason: BBKO21's notion for finite templates
-- source:
--   Cai, Jiang, Zou, On Robust Promise CSPs: A Boolean Dichotomy, Sharp Quantitative Bounds, and Soft-Equality Transfer, STOC 2027 submission (manuscript of 2026-11-03, sha256 fd1be0d0624155f00f7a115874a4dadfb7ebb2d4187530c7d0bdd4e1406e8732), Theorem 5.20, p.42

import Mathlib
import Definitions.Def_RobustBoolPCSP_ModeProperty
import Definitions.Def_RobustBoolPCSP_Supplement_PPConstruction

set_option autoImplicit false

namespace RobustBoolPCSP.Supplement

open RobustBoolPCSP

/-- **Theorem 5.20 (A majority condition forced by mode certificates)**, p.42. Cai, Jiang, Zou, *On Robust Promise CSPs*, STOC 2027 submission (manuscript of 2026-11-03,
sha256 fd1be0d0…).
"If a template has the mode property with output map h, then f = h ◦ d and u = h satisfy Σmaj in its
polymorphism minion, where d(x, y, z) = y if y = z and d(x, y, z) = x otherwise. Consequently, every
template in PP(MC) satisfies Σmaj." Here Σmaj is (46): "f(x, x, y) = f(x, y, x) = f(y, x, x) = u(x)".

**Formalization Note.** The first part: `h ∘ d` (ternary) and `h` (unary) are polymorphisms and obey
the identities (46). `PP(MC)` is pp-constructibility [BBKO21] from a finite member of `MC`
(`InPPMC`); `SatisfiesSigmaMaj` asks for a ternary and a unary polymorphism obeying (46). -/
theorem theorem_5_20 :
    (∀ {ι A B : Type} [Fintype A] [DecidableEq A] (T : Template ι A B) (h : A → B),
      (∀ j, ModeProperty (T.P j) (pullback T h j)) →
        IsPol T (fun x : Fin 3 → A => h (dMaj x)) ∧ IsPol T (fun x : Fin 1 → A => h (x 0)) ∧
        ∀ x y : A, h (dMaj ![x, x, y]) = h x ∧ h (dMaj ![x, y, x]) = h x ∧
          h (dMaj ![y, x, x]) = h x) ∧
    (∀ {ι A B : Type} (T : Template ι A B), InPPMC T → SatisfiesSigmaMaj T) := by sorry

end RobustBoolPCSP.Supplement
