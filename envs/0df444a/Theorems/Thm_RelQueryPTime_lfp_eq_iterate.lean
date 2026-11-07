-- Prove2me | Theorems.Thm_RelQueryPTime_lfp_eq_iterate
-- name    : RelQueryPTime.lfp_eq_iterate
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:40:06.37681+00:00
-- url     : https://prove2.me/theorems/fa93d285-87cf-4dfa-a21e-d1ea350af22b
-- title:
--   Proof of Proposition 1 — $\mathrm{LFP}(\varphi) = \varphi^{[n^a]}(\emptyset)$
-- statement:
--   Let $\varphi$ be a formula monotone in an $a$-ary relation variable $S$, let $B$ be an ordered database with $n$ elements, and fix values for all other variables. Write $F(S) = \{\bar u \mid B \models \varphi(S)[\bar u]\}$ for the operator on $a$-ary relations, the tuple $\bar u$ being assigned to the head variables. Then
--   $$
--   R_0 = F^{[n^a]}(\emptyset)
--   $$
--   satisfies
--   1. $F(R_0) = R_0$;
--   2. $R_0 \subseteq S$ for every relation $S$ with $F(S) \subseteq S$;
--   3. for every tuple of variables $\bar v$, $B \models \mathrm{LFP}(\varphi)(\bar v)$ iff the value of $\bar v$ lies in $R_0$.
--
--   So the least fixpoint is reached after at most $n^a$ iterations from the empty relation. This bound is what makes least fixpoints computable in polynomial time.
--
--   Differences from the source:
--   - generalization: φ(R)[x1…xa], a first-order operator with distinct head variables and no parameters → any formula monotone in the relation variable (nested LFP allowed), any head-variable map (not necessarily injective), other variables and relation variables fixed by the assignments; reason: the iteration argument uses only monotonicity and the bound of n^a tuples; the page's operator is an instance
--   - encoding: R0 = LFP(φ) → R0 is a fixed point, contained in every relation closed under the operator, and agrees with the LFP semantics at every tuple of variables; reason: Lean has no primitive least fixpoint of a formula; the three clauses say that R0 is the least fixpoint
-- source:
--   N. Immerman, Relational Queries Computable in Polynomial Time (Extended Abstract), Proc. 14th ACM STOC, 1982, pp.147–152, doi:10.1145/800070.802187, proof of Proposition 1, p.148 ("Define R0 = φ[n^a](∅) … Obviously R0 = LFP(φ) …") (PDF p.2)

import Mathlib
import Definitions.Def_RelQueryPTime_Syntax

namespace RelQueryPTime

/-- The least fixpoint is reached after `n^a` iterations (Immerman, *Relational Queries Computable in Polynomial Time*, STOC 1982, proof of Proposition 1, p.148):
for an operator `F(S) = φ(S)` monotone in the `a`-ary relation variable `j`, on a database with `n`
elements, `R₀ = F^[n^a](∅)` is a fixed point of `F`, is contained in every relation closed under
`F` (so it is the least fixpoint), and `LFP(φ)(v)` holds iff the value of `v` lies in `R₀`.

**Formalization Note** The head variables `hd` need not be distinct; the operator acts on
`a`-tuples assigned to them by `Env.bind`. Other free variables of `φ` are parameters fixed by `ρ`,
and other relation variables by `Ξ`. -/
theorem lfp_eq_iterate {σ : Schema} (j a : ℕ) (hd : Fin a → ℕ) (φ : Formula σ)
    (hmono : MonotoneIn j a φ) {n : ℕ} (B : Database σ n) (ρ : Env n) (Ξ : RelEnv n) :
    let F : ((Fin a → Fin n) → Prop) → ((Fin a → Fin n) → Prop) :=
      fun S u => φ.eval B (ρ.bind hd u) (Ξ.set j a S)
    F (F^[n ^ a] (fun _ => False)) = F^[n ^ a] (fun _ => False) ∧
    (∀ S : (Fin a → Fin n) → Prop, (∀ u, F S u → S u) →
      ∀ u, F^[n ^ a] (fun _ => False) u → S u) ∧
    ∀ vs : Fin a → ℕ, (Formula.lfp j a hd φ vs).eval B ρ Ξ ↔
      ∃ t, Matches ρ vs t ∧ F^[n ^ a] (fun _ => False) t := by sorry

end RelQueryPTime
