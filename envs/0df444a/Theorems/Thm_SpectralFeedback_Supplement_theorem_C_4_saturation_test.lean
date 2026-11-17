-- Prove2me | Theorems.Thm_SpectralFeedback_Supplement_theorem_C_4_saturation_test
-- name    : SpectralFeedback.Supplement.theorem_C_4_saturation_test
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T13:57:09.577304+00:00
-- url     : https://prove2.me/theorems/e08abcd2-86bf-46ef-8dc8-97e87e6ee445
-- title:
--   Theorem C.4 — exact saturation test: $\chi(q)$ with $\le m$ symbols $\iff$ orbit sum $\iff$ hive system at $x=q/m$
-- statement:
--   Let $\rho$ be a density matrix on $\mathbb C^d$, $n=\operatorname{rank}\rho$, $\lambda$ its positive spectrum, $r\ge1$, $r'=\min\{r,n\}$, and let $q=q^{(r')}(\lambda)$ be the least rank-$r'$ majorant. Suppose $r'\ge2$. For every $m\ge1$ the following are equivalent:
--
--   1. the unlimited value $\chi(q)$ is attainable with at most $m$ transmitted symbols, i.e. there are $A_1,\dots,A_m\succeq0$ with $\sum_hA_h=\rho$ and $\sum_hf_r(A_h)=\chi(q)$;
--   2. for some unitaries $U_h$ on the support of $\rho$,
--   $$
--   \rho=\frac1m\sum_{h=1}^mU_h\operatorname{diag}(q)U_h^*;\qquad\text{(C.15)}
--   $$
--   3. the linear hive system (C.10) is feasible with $x=q/m$.
--
--   Moreover, the least number of symbols attaining $\chi(q)$ exists and lies between $1$ and $n$. By the equivalence it is the least $m$ for which the hive system at $x=q/m$ is feasible, a linear feasibility problem with rational data when $\lambda$ is rational.
--
--   Differences from the source:
--   - generalization: receiver rank r ≤ d → any r ≥ 1; reason: r′ = min{r, n} and f_r are unchanged for r > d; for r ≤ d it is the source's statement
--   - encoding: χ(q) attainable with at most m transmitted symbols → χ(q) ∈ rewardSet r χ_r m ρ (m atoms, zero atoms allowed); reason: an atom may be zero, which is an unused symbol
--   - encoding: unitaries U_h on the support of ρ → a fixed isometry W : ℂ^n → ℂ^d with W*W = I_n and WW*ρ = ρ, and unitaries U_h of ℂ^n, with ρ = (1/m) Σ W U_h diag(q) U_h* W*; reason: W identifies the support of ρ with ℂ^n
--   - reading: for rational λ, the minimum can therefore be determined by rational LP feasibility, with 1 ≤ m ≤ n → the least attaining m₀ exists and 1 ≤ m₀ ≤ n (with the equivalence, m₀ is the least m whose hive system at x = q/m is feasible); reason: the sentence's mathematical content; the algorithmic reading has no stated model of computation
-- source:
--   Qi, Spectral Structure and Exact Arithmetic of Finite-Feedback Measurement Discrimination, manuscript (Nov. 2026; PDF sha256 a5b5cf40…eabde9cf), Theorem C.4, (C.15), p.30 (PDF p.32); notation §C.3–C.4, pp.27, 29

import Mathlib
import Definitions.Def_SpectralFeedback_rewardSet
import Definitions.Def_SpectralFeedback_Supplement_chi
import Definitions.Def_SpectralFeedback_Supplement_leastMajorant
import Definitions.Def_SpectralFeedback_Supplement_socpValues

open scoped ComplexOrder

namespace SpectralFeedback

namespace Supplement

/-- **Theorem C.4** (Exact saturation test; Qi, *Spectral Structure and Exact Arithmetic of
Finite-Feedback Measurement Discrimination*, manuscript (Nov. 2026), p.30 (PDF p.32)). Suppose
`r′ ≥ 2`. The unlimited value `χ(q)` is attainable with at most `m` transmitted symbols if and only if
`ρ = (1/m) ∑_{h=1}^m U_h diag(q) U_h*` (C.15) for some unitaries on its support. Equivalently, the
linear hive system (C.10) is feasible with `x = q/m`. For rational `λ`, the minimum can therefore be
determined by rational LP feasibility, with `1 ≤ m ≤ n`.

**Formalization Note** Notation of §C.3–C.4 (pp.27, 29): `ρ` is a density matrix, `n = rank ρ`,
`λ` its positive spectrum (`eigDesc ρ i`, `i < n`), `r′ = min{r, n}`, `q` the least rank-`r′`
majorant (`leastMajorant`). "Attainable with at most `m` symbols" is `χ(q) ∈ rewardSet r χ_r m ρ`
(`m` atoms, zero atoms allowed). "Unitaries on its support": a fixed isometry `W : ℂ^n → ℂ^d` onto
the range of `ρ` (`W* W = I_n`, `W W* ρ = ρ`) and unitaries `U_h` of `ℂ^n`. The last sentence is read
as: the least attaining `m` exists and lies in `[1, n]` (by the two equivalences it is the least `m`
for which (C.10) at `x = q/m` is feasible, a linear system with rational data when `λ` is
rational). -/
theorem theorem_C_4_saturation_test (r : ℕ) (hr : 1 ≤ r) {d : ℕ}
    (ρ : Matrix (Fin d) (Fin d) ℂ) (hρ : ρ.PosSemidef) (htr : ρ.trace = 1)
    (hr' : 2 ≤ min r ρ.rank) :
    (∀ m : ℕ, 1 ≤ m →
      ((chi ρ.rank (leastMajorant (eigDesc ρ) ρ.rank (min r ρ.rank)) ∈ rewardSet r (chi r) m ρ ↔
        ∃ W : Matrix (Fin d) (Fin ρ.rank) ℂ, ∃ U : Fin m → Matrix (Fin ρ.rank) (Fin ρ.rank) ℂ,
          W.conjTranspose * W = 1 ∧ W * W.conjTranspose * ρ = ρ ∧
          (∀ h, U h ∈ Matrix.unitaryGroup (Fin ρ.rank) ℂ) ∧
          ρ = ((m : ℂ)⁻¹) • ∑ h, W * U h *
            Matrix.diagonal (fun i => ((leastMajorant (eigDesc ρ) ρ.rank (min r ρ.rank) i : ℝ) : ℂ)) *
              star (U h) * W.conjTranspose) ∧
      (chi ρ.rank (leastMajorant (eigDesc ρ) ρ.rank (min r ρ.rank)) ∈ rewardSet r (chi r) m ρ ↔
        HiveChain ρ.rank m (fun i => leastMajorant (eigDesc ρ) ρ.rank (min r ρ.rank) i / (m : ℝ))
          (fun i => eigDesc ρ (i : ℕ))))) ∧
    ∃ m₀ : ℕ, 1 ≤ m₀ ∧ m₀ ≤ ρ.rank ∧
      chi ρ.rank (leastMajorant (eigDesc ρ) ρ.rank (min r ρ.rank)) ∈ rewardSet r (chi r) m₀ ρ ∧
      ∀ m : ℕ, 1 ≤ m → m < m₀ →
        chi ρ.rank (leastMajorant (eigDesc ρ) ρ.rank (min r ρ.rank)) ∉ rewardSet r (chi r) m ρ := by sorry

end Supplement

end SpectralFeedback
