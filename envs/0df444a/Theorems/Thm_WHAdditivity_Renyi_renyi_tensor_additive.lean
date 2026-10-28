-- Prove2me | Theorems.Thm_WHAdditivity_Renyi_renyi_tensor_additive
-- name    : WHAdditivity.Renyi.renyi_tensor_additive
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:26:14.353471+00:00
-- url     : https://prove2.me/theorems/5c0523c2-fc76-4f8f-8e40-9647082a6424
-- title:
--   p. 2 — the von Neumann and p-Rényi entropies are additive on tensor products
-- statement:
--   Let $N\in\mathbb N$, let $d_1,\dots,d_N$ be dimensions, let $\rho_j$ be a density matrix on $\mathbb C^{d_j}$ for each $j$, and let $p\ge1$. Then
--
--   $$S_p\Bigl(\bigotimes_{j=1}^N\rho_j\Bigr) = \sum_{j=1}^N S_p(\rho_j),$$
--
--   where $S_p(\rho) = -\frac{1}{p-1}\log\operatorname{Tr}\rho^p$ for $p>1$ and $S_1 = S$ is the von Neumann entropy (natural logarithm). The case $p = 1$ is additivity of the von Neumann entropy, the case $p>1$ additivity of the Rényi entropies.
--
--   In the paper this is the remark that reduces the additivity conjecture to the inequality (5); in the proof of (7) it gives the easy half: product inputs $\Omega = \bigotimes_j\varphi_j$ already achieve $\sum_j\mathrm{MEO}_p[\Gamma_{d_j}]$.
--
--   **Formalization Note.** $\bigotimes_j\rho_j$ is the matrix on $\bigotimes_j\mathbb C^{d_j}$ with entries $\prod_j(\rho_j)_{y_j y'_j}$, in the product basis.
--
--   Differences from the source:
--   - generalization: "additive on tensor products" (no number of factors, used for two in (5)) → N-fold products with arbitrary dimensions d_j; reason: contains the two-fold case (N = 2), and the N-fold case is what (7) uses.
--   - encoding: S_p for p > 1, extended to p = 1 by the limit → S_1 := S; reason: the limit's value is S; p = 1 is the von Neumann case of the remark.
--   - encoding: log unspecified → natural logarithm; reason: additivity holds in every base.
-- source:
--   Alicki, Fannes, Note on multiple additivity of minimal Renyi entropy output of the Werner–Holevo channels, arXiv:quant-ph/0407033v2, p. 2, remark before (5)

import Mathlib
import Definitions.Def_WHAdditivity_Renyi_Model

namespace WHAdditivity.Renyi

theorem renyi_tensor_additive (N : ℕ) (d : Fin N → ℕ)
    (ρ : (j : Fin N) → Matrix (Fin (d j)) (Fin (d j)) ℂ) (hρ : ∀ j, IsDensity (ρ j))
    (p : ℝ) (hp : 1 ≤ p) :
    renyiEntropy p (tensorMatrix d ρ) = ∑ j, renyiEntropy p (ρ j) := by sorry

end WHAdditivity.Renyi
