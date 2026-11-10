-- Prove2me | Theorems.Thm_RobersonCx_lemma_6
-- name    : RobersonCx.lemma_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:13:33.020537+00:00
-- url     : https://prove2.me/theorems/b45a2c33-9a41-4e64-856a-aa1a1d14d64a
-- title:
--   Lemma 6 — $\hom(F,X)\equiv\hom(F/\langle\sigma\rangle,X)\pmod p$ for an automorphism of prime order $p$
-- statement:
--   Let $F$ be a graph, $p$ a prime, and $\sigma$ an automorphism of $F$ of order $p$. Put $Q=F/\langle\sigma\rangle$, the orbit quotient (loops retained). Then for every graph $X$,
--   $$\hom(F,X)\equiv\hom(Q,X)\pmod p.$$
--   The congruence also holds when $Q$ has a loop, in which case $\hom(Q,X)=0$.
--
--   This quotient identity (Peyerimhoff, Roth, Schmitt, Stix, Vdovina) supplies the congruences fed into Proposition 5.
--
--   Differences from the source:
--   - encoding: $Q=F/\langle\sigma\rangle$ with loops retained and $\hom(Q,X)$ → the relation `quotRel` on the orbit type and the count `homCountQuot` of maps preserving it; reason: a `SimpleGraph` cannot carry loops; same counts
-- source:
--   Kristjánsson, Counterexamples to the Strong Roberson Conjecture, arXiv:2610.03550 (version of 2 November 2026, sha256 1b70a7c6…), Lemma 6, pp.7–8 (PDF pp.9–10)

import Mathlib
import Definitions.Def_RobersonCx_InCl
import Definitions.Def_RobersonCx_QuotIsoTo

set_option autoImplicit false

namespace RobersonCx

/-- Lemma 6 (Peyerimhoff–Roth–Schmitt–Stix–Vdovina) (Kristjánsson, *Counterexamples to the Strong Roberson Conjecture*, arXiv:2610.03550 (version of 2 November 2026, sha256 1b70a7c6…), §3, pp.7–8 (PDF pp.9–10)). Let `F` be a graph, `p` a
prime, and `σ` an automorphism of `F` of order `p`. Put `Q = F/⟨σ⟩`. Then for every graph `X`,
`hom(F, X) ≡ hom(Q, X) (mod p)`.

**Formalization Note** The order is `orderOf σ` in the group `F ≃g F`. `Q` is the orbit quotient with loops
retained (`quotRel` on the orbits of `⟨σ⟩`), and `hom(Q, X)` is `homCountQuot`; no looplessness is assumed
("This proves the asserted equivalence, also when Q has a loop", p.8). -/
theorem lemma_6 {V : Type} [Finite V] (F : SimpleGraph V) (p : ℕ) (hp : p.Prime) (σ : F ≃g F)
    (hσ : orderOf σ = p) (X : Type) [Finite X] (GX : SimpleGraph X) :
    homCount F GX ≡ homCountQuot F σ.toEquiv GX [MOD p] := by sorry

end RobersonCx
