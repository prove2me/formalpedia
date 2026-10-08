-- Prove2me | Theorems.Thm_PrivLearn_LocalSim_avg_is_private
-- name    : PrivLearn.LocalSim.avg_is_private
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:51:00.602892+00:00
-- url     : https://prove2.me/theorems/f7e54103-7aa7-44c3-966b-8fbd164921b5
-- title:
--   §5.1.1, p. 20 — the local algorithm A_g is ε-differentially private
-- statement:
--   Let $g:D\to[-b,b]$ with $b>0$, let $\varepsilon>0$ and $n\in\mathbb N$. The local algorithm $\mathcal A_g(n,\varepsilon,LR_z)$, which outputs
--   $$\frac1n\sum_{i=1}^n\bigl(g(z_i)+\eta_i\bigr),\qquad \eta_1,\dots,\eta_n\ \text{i.i.d.}\ \mathrm{Lap}(2b/\varepsilon),$$
--   is $\varepsilon$-differentially private as an algorithm on databases $z\in D^n$: for neighboring $z,z'$ and every Borel set $S\subseteq\mathbb R$, $\Pr[\mathcal A_g(z)\in S]\le e^{\varepsilon}\Pr[\mathcal A_g(z')\in S]$.
--
--   The paper's reason is that $\mathcal A_g$ applies a single $\varepsilon$-local randomizer to each entry. This is the privacy half of Theorem 5.7 for one query.
--
--   **Formalization Note.** The output law is the push-forward of the product of $n$ copies of $\mathrm{Lap}(2b/\varepsilon)$ under $\eta\mapsto\frac1n\sum_i(g(z_i)+\eta_i)$. For $n=0$ the output is the constant $0$ and the statement is trivial.
-- source:
--   Kasiviswanathan, Lee, Nissim, Raskhodnikova and Smith, What Can We Learn Privately?, arXiv:0803.0924v3, p. 20, §5.1.1, the paragraph after the box defining A_g

import Mathlib
import Definitions.Def_PrivLearn_LocalSim_Privacy
import Definitions.Def_PrivLearn_LocalSim_Simulation

namespace PrivLearn.LocalSim

open MeasureTheory

/-- §5.1.1 (p. 20): for a query `g : Dom → [−b, b]` and every database size `n`, the local
algorithm `A_g(n, ε, LR_z)`, which outputs `(1/n) ∑_i (g(z_i) + η_i)` with `η_i` i.i.d.
`Lap(2b/ε)`, is ε-differentially private. -/
theorem avg_is_private {Dom : Type*} (g : Dom → ℝ) (b ε : ℝ) (hb : 0 < b) (hε : 0 < ε)
    (hg : ∀ u, |g u| ≤ b) (n : ℕ) :
    PrivLearn.Generic.IsDP (fun z : Fin n → Dom => avgRespLaw g b ε z) ε := by sorry

end PrivLearn.LocalSim
