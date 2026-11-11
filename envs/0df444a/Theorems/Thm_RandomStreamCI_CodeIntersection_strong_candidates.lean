-- Prove2me | Theorems.Thm_RandomStreamCI_CodeIntersection_strong_candidates
-- name    : RandomStreamCI.CodeIntersection.strong_candidates
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:29:06.191197+00:00
-- url     : https://prove2.me/theorems/219af1ea-e097-4ee3-a595-89e0f39754b8
-- title:
--   Lemma 16 — Total positive posterior mass of strong codewords
-- statement:
--   Let $C\subseteq\Sigma^n$ be $(\rho,\ell,L)$-list recoverable in the total-list sense, let $A\subseteq[n]\times\Sigma$, and let $X$ be a law on Boolean assignments to $A$. Fix $0<\gamma<1$, $0<\eta<1/2$, and $D\ge0$. If
--
--   $$H_\infty(X)\ge |A|-D,\qquad\frac{D+\log_2(1/\eta)}{1-\gamma}\le\ell,$$
--
--   then, writing $k_c=|T_c\cap A|$ and $[z]^+=\max(z,0)$,
--
--   $$\sum_{c\in C:k_c\ge\rho n+\log_2(1/\eta)/\gamma}[\Pr(X_{T_c\cap A}\equiv1)-2\eta]^+\le L.$$
--
--   The sum includes all codewords meeting the exact threshold. The statement supplies the posterior-mass estimate needed at a crossing event.
--
--   Differences from the source:
--   - encoding: coordinates and times numbered from one → Fin indices numbered from zero; reason: the order-preserving relabelling preserves every source instance
-- source:
--   Bouland–Ding–Jain, Exponential quantum space advantage in random data streams, STOC 2027 submission #71, preprint dated 2026-11-02, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/71.pdf, SHA256 3fe1835efedc1b9f29103379085d28d84ab1057dc30c3e3f05a8dce9f536a797, Lemma 16, printed p. 13 / PDF p. 13

import Definitions.Def_RandomStreamCI_CodeIntersection_Stream

noncomputable section

namespace RandomStreamCI.CodeIntersection

open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-- Lemma 16, p. 13 (44)–(45), total list budget and full positive-posterior sum. -/
theorem strong_candidates {n : ℕ} {Alphabet : Type} [Fintype Alphabet]
    [DecidableEq Alphabet] (C : Finset (Word n Alphabet)) (ρ ℓ L : ℝ)
    (hC : ListRecoverable C ρ ℓ L) (A : Finset (Address n Alphabet))
    (p : PMF (A → Bool)) (γ η D : ℝ)
    (hγ : 0 < γ) (hγ1 : γ < 1) (hη : 0 < η) (hη2 : η < 1 / 2) (hD : 0 ≤ D)
    (hentropy : (A.card : ℝ) - D ≤ minEntropy (weights p))
    (hbudget : (D + log₂ (1 / η)) / (1 - γ) ≤ ℓ) :
    (∑ c ∈ C.filter (fun c => ρ * n + log₂ (1 / η) / γ ≤ (observedCount c A : ℝ)),
      max (eventMass (weights p)
        (fun x => ∀ u : A, u.val ∈ wordAddresses c → x u = true) - 2 * η) 0) ≤ L := by sorry

end RandomStreamCI.CodeIntersection
