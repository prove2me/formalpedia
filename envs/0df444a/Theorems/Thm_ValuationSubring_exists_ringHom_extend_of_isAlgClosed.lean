-- Prove2me | Theorems.Thm_ValuationSubring_exists_ringHom_extend_of_isAlgClosed
-- name    : ValuationSubring.exists_ringHom_extend_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.105901+00:00
-- url     : https://prove2.me/theorems/dd7c5f46-b056-5631-91fc-54e530f88635
-- title:
--   Chevalley's extension theorem in place form
-- statement:
--   Let $L$ be a field, let $\Omega$ be an algebraically closed field, let $R$ be a subring of $L$, and let $\varphi \colon R \to \Omega$ be a ring homomorphism. The assertion is that there exist a valuation subring $\mathcal{O}$ of $L$ — that is, a subring of $L$ such that for every $x \in L$ either $x \in \mathcal{O}$ or $x^{-1} \in \mathcal{O}$ — together with a proof $h$ that $R$ is contained in the underlying subring of $\mathcal{O}$, and a ring homomorphism $\psi \colon \mathcal{O} \to \Omega$, such that two conditions hold: first, the composite of the inclusion $R \hookrightarrow \mathcal{O}$ determined by $h$ followed by $\psi$ equals $\varphi$, so that $\psi$ restricted to $R$ is $\varphi$; and second, the kernel of $\psi$ is exactly the maximal ideal of the local ring $\mathcal{O}$. Thus $\varphi$ is extended to a place of $L$ with values in $\Omega$, whose valuation ring contains $R$ and whose residue field embeds into $\Omega$.
--
--   This is Chevalley's extension theorem in its homomorphism, or place, form: it strengthens the usual domination statement (a local subring is dominated by some valuation subring) by producing an actual homomorphism to $\Omega$ whose kernel is the maximal ideal, which the domination form does not give, since a dominating valuation ring may have a transcendental residue extension. It is used in the construction of retractions onto valuation subrings and, through these, in the study of prolongations along algebraic curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_exists_ringHom_extend_of_isAlgClosed.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ValuationSubring.exists_ringHom_extend_of_isAlgClosed
    {L Ω : Type*} [Field L] [Field Ω] [IsAlgClosed Ω] (R : Subring L) (φ : R →+* Ω) :
    ∃ (O : ValuationSubring L) (h : R ≤ O.toSubring) (ψ : O →+* Ω),
      ψ.comp (Subring.inclusion h) = φ ∧ RingHom.ker ψ = IsLocalRing.maximalIdeal O := by sorry
