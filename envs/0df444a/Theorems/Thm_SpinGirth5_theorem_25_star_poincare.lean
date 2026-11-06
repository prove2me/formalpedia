-- Prove2me | Theorems.Thm_SpinGirth5_theorem_25_star_poincare
-- name    : SpinGirth5.theorem_25_star_poincare
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:12:57.929527+00:00
-- url     : https://prove2.me/theorems/d5dd99c8-6ca3-47bb-8f4c-9582b8a282ce
-- title:
--   Theorem 25 — Poincaré inequality on a star from $\|(P_v)_{00}\|<1/5$ and $\|(P_v)_{10}\|^2/((1-r)(1-4r))<1$
-- statement:
--   Let $\nu$ be a distribution on configurations of a star with centre $v$ and leaves $1,\dots,d$, under which the leaves are independent conditional on the centre colour, and work in $(\mathbf 1^\perp,\langle\cdot,\cdot\rangle_\nu)$ with $K_0=\operatorname{Ker}L_{N(v)}$, $K_1=\operatorname{Ker}(L_{N(v)}-I)$. Let $0\le r<1/5$ and $0\le\eta<1$ satisfy
--   $$\|(P_v)_{00}\|\le r,\qquad \|(P_v)_{10}\|^2\le\eta\,(1-r)(1-4r).$$
--   Then
--   $$\frac{1-\eta}{2}\,\langle f,f\rangle\le\Big\langle f,\Big(L_v+\frac{1+\eta}{2}L_{N(v)}\Big)f\Big\rangle\qquad\text{for all }f\in\mathbf 1^\perp .$$
--   The printed statement is the case $r=\|(P_v)_{00}\|$, $\eta=\|(P_v)_{10}\|^2/((1-r)(1-4r))$. It is the local spectral input of Theorem 20: Lemma 27 bounds the two block norms for the stars of a Gibbs distribution.
--
--   Differences from the source:
--   - generalization: r := ‖(P_v)₀₀‖ < 1/5 and η := ‖(P_v)₁₀‖²/((1 − r)(1 − 4r)) < 1 (exact values) → any r, η with 0 ≤ r < 1/5, 0 ≤ η < 1, ‖(P_v)₀₀‖ ≤ r and ‖(P_v)₁₀‖² ≤ η(1 − r)(1 − 4r); reason: equality is the printed case; for larger r the printed η is no larger, and (11) only gets weaker as η grows because L_{N(v)} ⪰ 0
--   - encoding: operator norms of blocks ‖·‖ (Definition 11) → quadratic-form bounds over h ∈ K₀, k ∈ K₁; reason: ‖(P_v)₀₀‖ is the top Rayleigh quotient of the positive semidefinite block on K₀; ‖proj_{K₁} g‖² ≤ c ⟺ ⟨g,k⟩² ≤ c⟨k,k⟩ for all k ∈ K₁
--   - encoding: configurations of the star N[v] in [q]^{N[v]} → maps Option (Fin d) → Fin q, centre none, leaves some i; L²(ν) as functions with the ν-weighted form; reason: a relabelling of N[v]; values off supp ν do not enter
-- source:
--   Chen, Liu, A Spectral Local-to-Global Principle for Spin Systems on Graphs with Girth At Least Five, arXiv:2608.25491, Theorem 25, Eq. (11), p.17 (§4, pp.16–17; Definition 24, p.17)

import Mathlib
import Definitions.Def_SpinGirth5_starModel

namespace SpinGirth5

/-- **Theorem 25** (Poincaré inequality on a star). Let `ν` be a distribution on `[q]^{N[v]}` for
a star with centre `v` and leaves `1, …, d`, such that the leaves are independent conditional on
the centre, and work in `(1⊥, ⟨·,·⟩_ν)`. Suppose `r ≥ ‖(P_v)₀₀‖` and `η ≥ ‖(P_v)₁₀‖²/((1−r)(1−4r))`
with `0 ≤ r < 1/5` and `0 ≤ η < 1`. Then
`((1 − η)/2) ⟨f, f⟩ ≤ ⟨f, (L_v + ((1 + η)/2) L_{N(v)}) f⟩` for every `f ∈ 1⊥`.

Chen, Liu, *A Spectral Local-to-Global Principle for Spin Systems on Graphs with Girth At Least
Five*, arXiv:2608.25491, Theorem 25, Eq. (11), p.17 (setting §4, pp.16–17; blocks, Definition 24,
p.17).

**Formalization Note** The centre is `none`, the leaves are `some i`. `(P_v)₀₀` is self-adjoint
and positive semidefinite on `K₀`, so `‖(P_v)₀₀‖ ≤ r` is `⟨h, P_v h⟩ ≤ r ⟨h, h⟩` on `K₀`;
`‖(P_v)₁₀‖² ≤ c` is `⟨P_v h, k⟩² ≤ c ⟨h, h⟩ ⟨k, k⟩` for `h ∈ K₀`, `k ∈ K₁`. The paper's
statement is the case `r = ‖(P_v)₀₀‖`, `η = ‖(P_v)₁₀‖²/((1−r)(1−4r))`. -/
theorem theorem_25_star_poincare {q d : ℕ} (ν : (Option (Fin d) → Fin q) → ℝ)
    (hν : MarkovMixing.IsDist ν) (hind : LeavesCondIndep ν) (r η : ℝ) (hr0 : 0 ≤ r)
    (hr : r < 1 / 5) (hη0 : 0 ≤ η) (hη : η < 1)
    (h00 : ∀ h, K0 ν h →
      MarkovMixing.innerPi ν h (heatBath ν none h) ≤ r * MarkovMixing.innerPi ν h h)
    (h10 : ∀ h k, K0 ν h → K1 ν k →
      MarkovMixing.innerPi ν (heatBath ν none h) k ^ 2 ≤
        η * ((1 - r) * (1 - 4 * r)) * MarkovMixing.innerPi ν h h * MarkovMixing.innerPi ν k k) :
    PoincareIneq ν (fun f x => singleLap ν none f x + (1 + η) / 2 * lapSum ν (leaves d) f x)
      ((1 - η) / 2) := by sorry

end SpinGirth5
