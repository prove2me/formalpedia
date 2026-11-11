-- Prove2me | Theorems.Thm_RandomStreamCI_CodeIntersection_potential_evolution
-- name    : RandomStreamCI.CodeIntersection.potential_evolution
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:31:31.999041+00:00
-- url     : https://prove2.me/theorems/91fb3514-c6cf-444f-afc1-322a60abb564
-- title:
--   Lemma 17 — Exact one-step potential growth under the space budget
-- statement:
--   Let $C$ be $(\rho,\ell,L)$-list recoverable, $B$ have width $w=2^S$ (so $S=\log_2 w$; $\ell,L$ real), $0<\gamma<1$ and $0<\eta<1/2$. Put $\kappa^*=\lceil\rho n+\log_2(1/\eta)/\gamma\rceil+1$ in the standing threshold domain $[n]$. If
--
--   $$S\le(1-\gamma)\ell-\log_2|C|-\log_2(1/\eta),$$
--
--   then for every $0\le t<M$,
--
--   $$\Psi_{\eta,\kappa^*}(t+1)-\Phi_{\eta,\kappa^*}(t)\le\frac{(L+1)(n-\kappa^*+1)2^{-(n-\kappa^*+1)}}{M-t}.$$
--
--   The denominator is positive in this time domain. The exact constant, ceiling, extra one, and negative exponent are retained in the finite-step estimate.
--
--   Differences from the source:
--   - encoding: coordinates and times numbered from one → Fin indices numbered from zero; reason: the order-preserving relabelling preserves every source instance
--   - encoding: threshold kappa in [n] and incoming edge time t in 1 through M → integer threshold with explicit bounds and Fin M indexing the edge arriving at time t.val + 1; reason: integer ceilings and real exponents avoid natural subtraction truncation and enumerate exactly the same times
--   - encoding: program of width w = 2^S, with the space budget S ≤ (1 − γ)ℓ − log|C| − log(1/η) → program of arbitrary width w (states Fin w), with S replaced by log₂ w; reason: S = log₂ w is the source's own relation; every source program (any width, integer or not S) is an instance and nothing else is added
-- source:
--   Bouland–Ding–Jain, Exponential quantum space advantage in random data streams, STOC 2027 submission #71, preprint dated 2026-11-02, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/71.pdf, SHA256 3fe1835efedc1b9f29103379085d28d84ab1057dc30c3e3f05a8dce9f536a797, Lemma 17, printed p. 14 / PDF p. 14

import Definitions.Def_RandomStreamCI_CodeIntersection_Potential

noncomputable section

namespace RandomStreamCI.CodeIntersection

open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-- Lemma 17, p. 14 (55)–(56), for width w = 2^S, i.e. S = log₂ w. Positive threshold is the standing domain in Definition 13; all subtraction in the bound is real. -/
theorem potential_evolution {n w : ℕ} {Alphabet : Type} [Fintype Alphabet]
    [DecidableEq Alphabet] (B : BranchingProgram n Alphabet w)
    (C : Finset (Word n Alphabet)) (ρ γ η ℓ L : ℝ)
    (hC : ListRecoverable C ρ ℓ L)
    (hγ : 0 < γ) (hγ1 : γ < 1) (hη : 0 < η) (hη2 : η < 1 / 2)
    (hκ : 1 ≤ crossingThreshold n ρ γ η)
    (hκn : crossingThreshold n ρ γ η ≤ (n : ℤ))
    (hspace : log₂ w ≤ (1 - γ) * ℓ - log₂ C.card - log₂ (1 / η))
    (t : Fin (Fintype.card (Address n Alphabet))) :
    edgePotential B C η (crossingThreshold n ρ γ η) t -
      vertexPotential B C η (crossingThreshold n ρ γ η) t.val ≤
        (L + 1) * ((n : ℝ) - (crossingThreshold n ρ γ η : ℝ) + 1) *
          (2 : ℝ) ^ (-((n : ℝ) - (crossingThreshold n ρ γ η : ℝ) + 1)) /
            ((Fintype.card (Address n Alphabet) : ℝ) - t.val) := by sorry

end RandomStreamCI.CodeIntersection
