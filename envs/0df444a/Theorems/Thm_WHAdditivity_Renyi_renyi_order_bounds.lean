-- Prove2me | Theorems.Thm_WHAdditivity_Renyi_renyi_order_bounds
-- name    : WHAdditivity.Renyi.renyi_order_bounds
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:26:00.900099+00:00
-- url     : https://prove2.me/theorems/22b1e080-02ad-4331-afa1-f0baab294c01
-- title:
--   p. 4 — S₂(ρ) ≤ Sₚ(ρ) ≤ S(ρ) for 1 ≤ p ≤ 2
-- statement:
--   Let $\rho$ be a density matrix (positive semidefinite, trace one) on a finite-dimensional complex Hilbert space, and let $1\le p\le 2$. With $S_p(\rho) = -\frac{1}{p-1}\log\operatorname{Tr}\rho^p$ for $p>1$, $S_1 = S$ and $S(\rho) = -\operatorname{Tr}\rho\log\rho$ the von Neumann entropy (natural logarithm),
--
--   $$S_2(\rho)\ \le\ S_p(\rho)\ \le\ S(\rho).$$
--
--   This is the inequality relating the $p$-Rényi entropies, the 2-Rényi entropy and the von Neumann entropy that the paper takes from Rényi [5]; with it the bound (8) on the purity $\operatorname{Tr}X^2 = e^{-S_2(X)}$ becomes a lower bound on every $S_p$, $1\le p\le2$.
--
--   **Formalization Note.** The space is indexed by an arbitrary finite type $\iota$. Both entropies are defined by Mathlib's continuous functional calculus.
--
--   Differences from the source:
--   - encoding: S_p for p > 1, extended to p = 1 by the limit → S_1 := S; reason: the limit's value is S, so at p = 1 the statement reads S_2 ≤ S ≤ S.
--   - encoding: log unspecified → natural logarithm; reason: the inequality is invariant under the choice of base.
-- source:
--   Alicki, Fannes, Note on multiple additivity of minimal Renyi entropy output of the Werner–Holevo channels, arXiv:quant-ph/0407033v2, p. 4, display after 'Finally, we use the inequality'

import Mathlib
import Definitions.Def_WHAdditivity_Renyi_Model

namespace WHAdditivity.Renyi

theorem renyi_order_bounds {ι : Type} [Fintype ι] [DecidableEq ι] (ρ : Matrix ι ι ℂ)
    (hρ : IsDensity ρ) (p : ℝ) (hp1 : 1 ≤ p) (hp2 : p ≤ 2) :
    renyiEntropy 2 ρ ≤ renyiEntropy p ρ ∧ renyiEntropy p ρ ≤ vonNeumannEntropy ρ := by sorry

end WHAdditivity.Renyi
