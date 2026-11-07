-- Prove2me | Theorems.Thm_SYKEdge_lemma_4_12
-- name    : SYKEdge.lemma_4_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T13:08:41.656895+00:00
-- url     : https://prove2.me/theorems/75502512-ba32-4607-bfb6-f05b8f014cf3
-- title:
--   Lemma 4.12 — spectral edge of the hopping model: $\lambda_{\max}(\Pi_Rx\Pi_R)\ge\frac2{\sqrt\nu}\big(1-O(1)\max\{\kappa^{-1},\nu^2\}\big)$
-- statement:
--   Let $\mathcal H$ be a $k$-uniform hypergraph with leakage parameters $q,\delta,\rho^-$, $\nu=1-q$, $B=\sqrt{\nu/(\rho^-+\delta)}$, $M=\lfloor1/\nu\rfloor$. Suppose $B\ge\kappa\ge\Omega_n(1)$ for a parameter $\kappa$, and write $t_0=\lceil\kappa/\nu\rceil$, $L=t_0+M$. Then for the Krylov space $R=R_{t_0,M}$
--   $$\lambda_{\max}(\Pi_Rx\Pi_R)\ \ge\ \frac2{\sqrt\nu}\Big(1-O(1)\cdot\max\{\kappa^{-1},\nu^2\}\Big).$$
--
--   This produces the witness value $\approx2/\sqrt\nu\approx\sqrt{2n}/k$ for the lower bound.
--
--   **Formalization Note** "$\kappa\ge\Omega_n(1)$" is $\kappa\ge\kappa_0$ for an absolute $\kappa_0>0$, and $O(1)$ is an absolute $C>0$; both are chosen before the hypergraph. $B\ge\kappa$ is written $(\rho^-+\delta)\kappa^2\le\nu$. $\lambda_{\max}(\Pi_Rx\Pi_R)$ is the supremum of $\langle\psi,x\psi\rangle$ over unit $\psi\in R$.
--
--   Differences from the source:
--   - encoding: the §3 standing assumptions (n ⩾ k ⩾ 2 even, ℋ a k-uniform hypergraph) → IsKUniform n k m S: the same, with ℋ = (S_1, …, S_m) an indexed list and m ⩾ 1; reason: repeated hyperedges are distinct elements (footnote 6); m ⩾ 1 is needed for |ℋ|^{−1/2} and only excludes the empty hypergraph
--   - reading: B ⩾ κ ⩾ Ω_n(1) → κ ⩾ κ₀ for an absolute κ₀ > 0 and (ρ⁻ + δ)κ² ⩽ ν, with κ₀ and the O(1) constant chosen before the hypergraph; reason: B ⩾ κ ⩾ 0 is κ² ⩽ ν/(ρ⁻ + δ), multiplied out so that ρ⁻ + δ = 0 (B = ∞) is included; Ω_n(1) is a lower bound by an absolute constant
--   - encoding: no hypothesis on q printed → 0 ⩽ q < 1; reason: exactly the condition that ν > 0 (so B, t₀, M are defined) and M = ⌊1/ν⌋ ⩾ 1 (so R ≠ 0 and λ_max(Π_R x Π_R) is defined); it is also Lemma 4.10's hypothesis, which the proof applies
--   - encoding: Write t₀ := ⌈κ/ν⌉, L := t₀ + M → t₀ only, with R = R_{t₀,M}; L does not appear; reason: L does not occur in the conclusion; it is notation for Lemmas 4.16 and 4.18
-- source:
--   Basu, Kothari, Midha, Sharp Bounds on Ground State Energy of the SYK Model, arXiv:2607.27185v2, Lemma 4.12, p.29; eq. (24) and Definition 4.11, p.28

import Mathlib
import Definitions.Def_SYKEdge_Krylov
import Definitions.Def_SYKEdge_Hamiltonian

namespace SYKEdge

/-- **Lemma 4.12** (Spectral edge of hopping model), A. Basu, P. K. Kothari, S. Midha, *Sharp Bounds on Ground State Energy of the SYK Model*,
arXiv:2607.27185v2, p.29.

Suppose `B ⩾ κ ⩾ Ω_n(1)` for some parameter `κ`, where `ν = 1 − q`, `B = √(ν/(ρ⁻ + δ))`,
`M = ⌊1/ν⌋` (24). Write `t₀ := ⌈κ/ν⌉`, `L := t₀ + M`. Then
`λ_max(Π_R x Π_R) ⩾ (2/√ν)·(1 − O(1)·max{κ^{−1}, ν²})` for `R = R_{t₀,M}`.

**Formalization Note.**
* `κ ⩾ Ω_n(1)` is `κ ⩾ κ₀` for an absolute `κ₀ > 0`; `O(1)` is an absolute `C > 0`; both are chosen
  before the hypergraph.
* `B ⩾ κ` is written `(ρ⁻ + δ)κ² ⩽ ν` (equivalent for `κ ⩾ 0`, and meaningful when `ρ⁻ + δ = 0`,
  where `B = ∞`).
* `0 ⩽ q < 1` is the hypothesis of Lemma 4.10, which this lemma's proof applies; it is exactly the
  condition that `ν > 0` (so `B`, `t₀` are defined) and `M = ⌊1/ν⌋ ⩾ 1` (so `R ≠ 0`).
* `λ_max(Π_R x Π_R)` is the supremum of `⟨ψ, xψ⟩` over unit `ψ ∈ R` (`lamMaxOn`). -/
theorem lemma_4_12 :
    ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (n k m : ℕ) (S : Fin m → Finset (Fin n)), IsKUniform n k m S →
        0 ≤ qParam S → qParam S < 1 →
        ∀ κ : ℝ, κ₀ ≤ κ → (rhoMinus S + deltaParam S) * κ ^ 2 ≤ nuParam S →
          2 / Real.sqrt (nuParam S) * (1 - C * max κ⁻¹ (nuParam S ^ 2)) ≤
            lamMaxOn S (krylovR S (t0Param S κ) (MParam S)) := by sorry

end SYKEdge
