-- Prove2me | Theorems.Thm_SYKEdge_lemma_4_10
-- name    : SYKEdge.lemma_4_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T13:08:33.081346+00:00
-- url     : https://prove2.me/theorems/337996f4-f308-45c9-b879-74986be37c73
-- title:
--   Lemma 4.10 — hopping amplitudes $\beta_t^2\ge(1-q^{t+1}-(\rho^-+\delta)t)/(1-q)$
-- statement:
--   Let $\mathcal H$ be a $k$-uniform hypergraph with leakage parameters $q,\delta,\rho^-$, and let $\beta_t=\|\psi_{t+1}\|/\|\psi_t\|$ with $\psi_t=(a^*)^tf_0$. Assume $0\le q<1$. Then for every $t\ge0$
--   $$\beta_t^2\ \ge\ \frac{1-q^{t+1}-(\rho^-+\delta)\,t}{1-q}.$$
--
--   For $t$ in a window of length about $1/(1-q)$ the amplitudes are therefore close to $(1-q)^{-1/2}$, which is what makes the Krylov hopping model's edge close to $2/\sqrt{1-q}$.
--
--   Differences from the source:
--   - encoding: the §3 standing assumptions (n ⩾ k ⩾ 2 even, ℋ a k-uniform hypergraph) → IsKUniform n k m S: the same, with ℋ = (S_1, …, S_m) an indexed list and m ⩾ 1; reason: repeated hyperedges are distinct elements (footnote 6); m ⩾ 1 is needed for |ℋ|^{−1/2} and only excludes the empty hypergraph
-- source:
--   Basu, Kothari, Midha, Sharp Bounds on Ground State Energy of the SYK Model, arXiv:2607.27185v2, Lemma 4.10, p.28

import Mathlib
import Definitions.Def_SYKEdge_Krylov
import Definitions.Def_SYKEdge_Hamiltonian

namespace SYKEdge

/-- **Lemma 4.10** (Lower bound on hopping amplitude), A. Basu, P. K. Kothari, S. Midha, *Sharp Bounds on Ground State Energy of the SYK Model*,
arXiv:2607.27185v2, p.28.

Assume `0 ⩽ q < 1`. Then `β_t² ⩾ (1 − q^{t+1} − (ρ⁻ + δ)t) / (1 − q)`.

**Formalization Note.** Stated for every `t ∈ ℕ`; `β_t = ‖ψ_{t+1}‖/‖ψ_t‖` with `ψ_t = (a*)^t f₀`, (21)–(23).
The hypergraph satisfies the §3 standing assumptions. -/
theorem lemma_4_10 {n k m : ℕ} (S : Fin m → Finset (Fin n)) (hS : IsKUniform n k m S)
    (hq0 : 0 ≤ qParam S) (hq1 : qParam S < 1) (t : ℕ) :
    (1 - qParam S ^ (t + 1) - (rhoMinus S + deltaParam S) * t) / (1 - qParam S) ≤
      betaK S t ^ 2 := by sorry

end SYKEdge
