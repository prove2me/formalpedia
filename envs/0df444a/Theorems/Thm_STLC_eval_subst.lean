-- Prove2me | Theorems.Thm_STLC_eval_subst
-- name    : STLC.eval_subst
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-21T01:44:47.64084+00:00
-- url     : https://prove2.me/theorems/1f9a3421-4b45-4607-ad0e-5710e080a9e2
-- title:
--   Substitution lemma for the set-valued semantics of the simply typed lambda calculus
-- statement:
--   The **substitution lemma** for the set-valued semantics of the simply typed lambda calculus.
--
--   Let $\Gamma$ and $\Delta$ be typing contexts, let $s$ be a substitution sending every variable $x : \tau$ of $\Gamma$ to a term $s(x)$ of type $\tau$ in context $\Delta$, and let $\rho$ be an environment for $\Delta$ in an interpretation $X$ of the base types. Evaluating $s$ in $\rho$ gives an environment on $\Gamma$:
--
--   $$
--   \rho_s(x) = \llbracket s(x) \rrbracket_\rho .
--   $$
--
--   The lemma says that substituting and then evaluating is evaluating in the induced environment: for every term $t$ of type $\tau$ in context $\Gamma$,
--
--   $$
--   \llbracket t[s] \rrbracket_\rho \;=\; \llbracket t \rrbracket_{\rho_s} .
--   $$
--
--   This is the semantic counterpart of the syntactic substitution lemma, and it is the step that makes $\beta$-reduction sound: the two sides are exactly the denotations of $(\lambda x.\,t)\,a$ and of $t[a/x]$. It is where the interpretation stops being merely compositional and becomes compatible with the term calculus; every semantic argument about the lambda calculus passes through it.
-- source:
--   Barendregt, The Lambda Calculus: Its Syntax and Semantics (1984), ch. 2, substitution lemma; Pierce, Types and Programming Languages (2002), ch. 9; standard in categorical semantics of the lambda calculus, cf. Lambek--Scott, Introduction to Higher Order Categorical Logic (1986), Part I

import Definitions.Def_STLC_core

namespace STLC

/-- **Substitution lemma.** Evaluating the substitution instance
`Tm.subst s t` of a term `t : Tm Γ τ` in an environment `ρ` for `Δ` is the same as
evaluating `t` in the environment `Env.subst s ρ` that `s` induces on `Γ`. -/
theorem eval_subst {X : Nat → Type} {Γ Δ : List Ty} (s : Sub Γ Δ) :
    ∀ {τ : Ty} (t : Tm Γ τ) (ρ : Env X Δ),
      Tm.eval (Tm.subst s t) ρ = Tm.eval t (Env.subst s ρ) := by
  sorry

end STLC
