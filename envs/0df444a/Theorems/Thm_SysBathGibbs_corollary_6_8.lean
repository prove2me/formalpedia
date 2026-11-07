-- Prove2me | Theorems.Thm_SysBathGibbs_corollary_6_8
-- name    : SysBathGibbs.corollary_6_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:37:02.211898+00:00
-- url     : https://prove2.me/theorems/f574b8d5-76fc-49d8-b916-a36a83d13473
-- title:
--   Corollary 6.8 — Second and fourth moments of Gibbs-centered sums
-- statement:
--   For all $C_0,c_0>0$ there is $C>0$ (depending on $\beta,q,C_0,c_0$; $\sigma=\beta/2$) such that the following holds for every chain (1.2) on $n\ge1$ sites. Let $F=\sum_xF_x$ and $G=\sum_xG_x$, where each $F_x$, $G_x$ is Gibbs-centered and, for $|u|\le\beta/4$ and $r\ge0$,
--   $$
--   \|B(-iu)\|_{\mathrm{op}}\le C_0,\qquad \|(\mathrm{id}-\mathcal E_{x,r})B(-iu)\|_{\mathrm{op}}\le C_0e^{-c_0r},\qquad B\in\{F_x,G_x\}.
--   $$
--   Then $\|F\|_{\rho_\beta}+\|G\|_{\rho_\beta}\le C\sqrt n$ and $\|FG\|_{\rho_\beta}+\|GF\|_{\rho_\beta}\le Cn$; the same bounds hold when $F$, $G$ or both are replaced by their adjoints; and for every $t\in\mathbb R$,
--   $$
--   \|FG(t)\|_{\rho_\beta}+\|G(t)F\|_{\rho_\beta}\le Cn.
--   $$
--
--   Differences from the source:
--   - encoding: σ a free parameter of (1.4)–(1.8) → σ = β/2 throughout; reason: the paper fixes σ = β/2 throughout (p.10); no other width is stated
--   - encoding: a chain [n] of qudits of dimension 2^q → n ≥ 1 and q ≥ 1 as hypotheses; reason: a chain has a site and a qudit has q ≥ 1 qubits; Q = 4^q − 1 ≥ 1 is used throughout
--   - encoding: "the same bounds hold for adjoints" → (6.18) for each of F or F†, and G or G†; reason: the four combinations; F, G themselves are one of them
--   - encoding: sup_{t∈ℝ}(…) ≤ Cn → for every t ∈ ℝ, (…) ≤ Cn; reason: equivalent
-- source:
--   Ding, Li, Zhang, Efficient thermalization of one-dimensional noncommuting Hamiltonians via system-bath interactions with Θ(n) ancilla qubits, arXiv:2611.03422 (held file sha256 a60a3c09826df3b5399a5589f83ef3a1d2ea768d74c5e39e8a3b29d1323f024f), Corollary 6.8 (eqs. (6.17)–(6.19)), p.51

import Definitions.Def_SysBathGibbs_Coefficient

open Matrix MeasureTheory

namespace SysBathGibbs

/-- **Corollary 6.8 (Second and fourth moments)**, Ding, Li, Zhang, arXiv:2611.03422 (held file sha256 a60a3c09…), p.51.
Let `F = ∑_x F_x`, `G = ∑_x G_x` with Gibbs-centered terms whose imaginary-time evolutions for
`|u| ≤ β/4` are quasi-local at `x`, (6.17). Then `‖F‖ + ‖G‖ ≤ C√n`, `‖FG‖ + ‖GF‖ ≤ Cn`, the same bounds
hold for adjoints, and `sup_t (‖FG(t)‖ + ‖G(t)F‖) ≤ Cn`.

**Formalization Note.** "The same bounds hold for adjoints" is stated for each choice of `F` or `F†` and
of `G` or `G†`, written `adjIf a F`, `adjIf b G`; the case `a = b = false` is (6.18) itself. The final
`C` depends on `β, q` and the constants of (6.17). The norms are `kmsNorm`, and `sup_t` is a `∀ t`. -/
theorem corollary_6_8 :
    ∀ (β : ℝ), 0 < β → ∀ q : ℕ, 1 ≤ q → ∀ C₀ c₀ : ℝ, 0 < C₀ → 0 < c₀ →
      ∃ C : ℝ, 0 < C ∧
        ∀ (n : ℕ), 1 ≤ n → ∀ h : Fin (n - 1) → SysMat n q, IsChain h →
          ∀ F G : Fin n → SysMat n q,
            IsCenteredQuasiLocal β (chainHam h) C₀ c₀ F →
            IsCenteredQuasiLocal β (chainHam h) C₀ c₀ G →
            (∀ a b : Bool,
              let F' : SysMat n q := if a then (∑ x, F x)ᴴ else ∑ x, F x;
              let G' : SysMat n q := if b then (∑ x, G x)ᴴ else ∑ x, G x;
              kmsNorm β (chainHam h) F' + kmsNorm β (chainHam h) G' ≤ C * Real.sqrt n ∧
              kmsNorm β (chainHam h) (F' * G') + kmsNorm β (chainHam h) (G' * F') ≤ C * n) ∧
            ∀ t : ℝ,
              kmsNorm β (chainHam h) ((∑ x, F x) * evo (chainHam h) t (∑ x, G x)) +
                kmsNorm β (chainHam h) (evo (chainHam h) t (∑ x, G x) * ∑ x, F x) ≤ C * n := by sorry

end SysBathGibbs
