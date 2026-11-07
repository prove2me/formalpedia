-- Prove2me | Theorems.Thm_QMAPlusGap_proposition_9
-- name    : QMAPlusGap.proposition_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T04:09:57.666279+00:00
-- url     : https://prove2.me/theorems/b4600f25-4a5d-4ab9-b581-b22df2e823f7
-- title:
--   Proposition 9 — soundness bound $1/4+\mathrm{poly}(\log M)M^{-\Omega_r(1)}$
-- statement:
--   Let $\mathcal H$ have a fixed computational basis and let $0\preceq B\preceq I$ satisfy $\sup_{|\psi\rangle\ge0,\ \||\psi\rangle\|=1}\langle\psi|B|\psi\rangle\le r<1$. Let $\rho^{(1)}_M,\rho^{(2)}_M\in\mathrm D(\mathrm{Sym}^M(\mathcal H))$ be entrywise nonnegative. For sufficiently large $M$ set $N=2\lfloor\tfrac14\log_2M\rfloor$ and let $\rho^{(1)}_N,\rho^{(2)}_N$ be the reductions to $N$ registers. Then
--   $$
--   \operatorname{Tr}\Big[P^{(2N)}_{\mathrm{sym}}B^{\otimes2N}\big(\rho^{(1)}_N\otimes\rho^{(2)}_N\big)\Big]\ \le\ \frac14+\mathrm{poly}(\log M)\,M^{-\Omega_r(1)},\tag{5}
--   $$
--   where the implicit constants depend only on $r$. Precisely: for every $r<1$ there are $C\ge0$, $k\in\mathbb N$, $\kappa>0$ and $M_0$ such that for every $\mathcal H=\mathbb C^\iota$, every such $B$, every $M\ge M_0$ and all such states, the left-hand side is at most $\tfrac14+C(\log M)^kM^{-\kappa}$.
--
--   This is the soundness core of the two-proof protocol: the symmetric test followed by $B$ on every register accepts entrywise nonnegative symmetric states with probability barely above $1/4$.
--
--   Differences from the source:
--   - reading: for sufficiently large M; poly(log M) M^{−Ω_r(1)}; implicit constants depending only on r → M ≥ M₀ and the bound C (log M)^k M^{−κ}, with C ≥ 0, k, κ > 0, M₀ depending only on r and chosen before ℂ^ι, B, M and the states; reason: the paper's statement of which constants depend on what
--   - encoding: the trace Tr[P B^{⊗2N}(ρ⊗ρ)]; 2N registers → its real part; Fin (N + N) registers with ρ^{(1)}_N on the first N; reason: P_sym and B^{⊗2N} commute and are positive, so the trace is real
-- source:
--   Miyamoto, Near-Optimal Gap Amplification for Nonnegative Unentangled Quantum Proofs, arXiv:2608.07986 (held version, sha256 4667925f…), Proposition 9, p.15

import Mathlib
import Definitions.Def_QMAPlusGap_IsNonnegVec
import Definitions.Def_QMAPlusGap_IsEntrywiseNonneg
import Definitions.Def_ArgmaxDeFinetti_vnorm
import Definitions.Def_QMAPlusGap_expect
import Definitions.Def_QMAPlusGap_symProj
import Definitions.Def_QMAPlusGap_IsSymSupported
import Definitions.Def_QMAPlusGap_reduce
import Definitions.Def_QMAPlusGap_tensorJoin
import Definitions.Def_WildeQIT_Schumacher_tensorPow
import Definitions.Def_WildeQIT_IsDensityOperator

set_option autoImplicit false

open scoped MatrixOrder ComplexOrder
open MeasureTheory Filter

namespace QMAPlusGap

/-- **Proposition 9 (Soundness bound for the two-proof test)**, Miyamoto, *Near-Optimal Gap Amplification for Nonnegative Unentangled Quantum Proofs*, arXiv:2608.07986 (held version, sha256 4667925f…), p.15: "Let H have a fixed computational basis,
and let 0 ⪯ B ⪯ I satisfy sup_{|ψ⟩≥0, ∥|ψ⟩∥=1} ⟨ψ|B|ψ⟩ ≤ r < 1. Let ρ_M^{(1)}, ρ_M^{(2)} ∈ D(Sym^M(H)) be entrywise
nonnegative density operators. For sufficiently large M, set N = 2⌊(1/4) log₂ M⌋, and let ρ_N^{(1)} and ρ_N^{(2)} be
their reductions to N registers. Then Tr[P_sym^{(2N)} B^{⊗2N} (ρ_N^{(1)} ⊗ ρ_N^{(2)})] ≤ 1/4 + poly(log M) M^{−Ω_r(1)}.
(5) The implicit constants depend only on r."

**Formalization Note** `poly(log M) M^{−Ω_r(1)}` is `C (log M)^k M^{−κ}` with `C ≥ 0`, `k`, `κ > 0` and the
threshold `M₀` ("sufficiently large M") depending only on `r`, all chosen before `H = ℂ^ι`, `B`, `M` and the
states (uniform in `dim H`). The `2N` registers are `Fin (N + N)`, the first `N` carrying `ρ_N^{(1)}`. The trace is
real (`P_sym^{(2N)}` and `B^{⊗2N}` commute); its real part is bounded. -/
theorem proposition_9 (r : ℝ) (hr : r < 1) :
    ∃ (C : ℝ) (k : ℕ) (κ : ℝ) (M₀ : ℕ), 0 ≤ C ∧ 0 < κ ∧
      ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (B : Matrix ι ι ℂ), B.PosSemidef → (1 - B).PosSemidef →
        (∀ ψ : ι → ℂ, IsNonnegVec ψ → ArgmaxDeFinetti.vnorm ψ = 1 → (expect B ψ).re ≤ r) →
        ∀ M N : ℕ, M₀ ≤ M → N = 2 * ⌊(1 / 4 : ℝ) * Real.logb 2 M⌋₊ →
        ∀ ρ₁ ρ₂ : Matrix (Fin M → ι) (Fin M → ι) ℂ,
          WildeQIT.IsDensityOperator ρ₁ → IsSymSupported ρ₁ → IsEntrywiseNonneg ρ₁ →
          WildeQIT.IsDensityOperator ρ₂ → IsSymSupported ρ₂ → IsEntrywiseNonneg ρ₂ →
          (Matrix.trace (symProj (N + N) * WildeQIT.Schumacher.tensorPow (N + N) B *
              tensorJoin (reduce N ρ₁) (reduce N ρ₂))).re ≤
            1 / 4 + C * Real.log M ^ k * (M : ℝ) ^ (-κ) := by sorry

end QMAPlusGap
