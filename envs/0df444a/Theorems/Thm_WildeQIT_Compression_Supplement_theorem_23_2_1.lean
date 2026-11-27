-- Prove2me | Theorems.Thm_WildeQIT_Compression_Supplement_theorem_23_2_1
-- name    : WildeQIT.Compression.Supplement.theorem_23_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T04:19:53.030141+00:00
-- url     : https://prove2.me/theorems/47787f2b-1653-518f-a02f-5ca90d3f4cbf
-- title:
--   Theorem 23.2.1 (Devetak–Cai–Winter–Yeung): $C_P(\mathcal N)=P_{\mathrm{reg}}(\mathcal N)$
-- statement:
--   The private classical capacity of a quantum channel $\mathcal N_{A'\to B}$ equals its regularized private information:
--
--   $$
--   C_P(\mathcal N)=P_{\mathrm{reg}}(\mathcal N)=\lim_{k\to\infty}\frac1kP(\mathcal N^{\otimes k}),
--   $$
--
--   where $P(\mathcal N)=\max_\rho[I(X;B)_\sigma-I(X;E)_\sigma]$ is the private information, the maximum over classical–quantum inputs $\rho_{XA'}=\sum_xp_X(x)|x\rangle\langle x|_X\otimes\rho^x_{A'}$ with $\sigma_{XBE}=U^{\mathcal N}_{A'\to BE}(\rho_{XA'})$.
--
--   The statement includes that the limit exists.
--
--   **Formalization Note** $C_P$ is `privateCapacity` (extended-real supremum of the rates of `IsAchievablePrivateRate`), $P$ the published `WildeQIT.Degradable.privateInfoChannel`, $\mathcal N^{\otimes k}$ the published `WildeQIT.Degradable.tensorPower`. The convergence of $\frac1kP(\mathcal N^{\otimes k})$ to $C_P(\mathcal N)$ is stated in the extended reals.
--
--   Differences from the source:
--   - encoding: C_P(N) = P_reg(N) with P_reg(N) ≡ lim_k (1/k) P(N^{⊗k}) → Tendsto (fun k => P(N^{⊗k})/k) atTop (nhds (privateCapacity N)) in EReal; reason: asserts that the limit exists and equals C_P(N), without a default value for a nonexistent limit
--   - encoding: Hilbert spaces of positive dimension (implicit) → `[Nonempty a]` on the input space; reason: a zero-dimensional space has no state, and the suprema defining the quantities would be empty; the hypothesis excludes only that case
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Theorem 23.2.1, p. 642, eqs. (23.13)–(23.16); §23.1, pp. 640–641

import Mathlib
import Definitions.Def_WildeQIT_Compression_Supplement_privateCapacity
import Definitions.Def_WildeQIT_Degradable_privateInfoChannel
import Definitions.Def_WildeQIT_Degradable_tensorPower

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, Theorem 23.2.1, p. 642.
-/

namespace WildeQIT.Compression.Supplement

/-- **Theorem 23.2.1 (Devetak–Cai–Winter–Yeung)** (Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, p. 642, (23.13)–(23.16)): "The private
classical capacity `C_P(N)` of a quantum channel `N_{A′→B}` is equal to the regularized private
information of the channel: `C_P(N) = P_reg(N)`, where `P_reg(N) ≡ lim_{k→∞} (1/k) P(N^{⊗k})`. The
private information `P(N)` is defined as `P(N) ≡ max_ρ [I(X;B)_σ − I(X;E)_σ]`, where `ρ_XA′` is a
classical–quantum state … and `σ_XBE ≡ U^N_{A′→BE}(ρ_XA′)`."

Formalization Note: the limit is asserted to exist and to equal `C_P(N)`: the sequence
`(1/k) P(N^{⊗k})` converges in `EReal` to `C_P(N)`. `C_P(N)` is `privateCapacity` (the `EReal`
supremum of the rates of `IsAchievablePrivateRate`, §23.1); `P` is the published
`WildeQIT.Degradable.privateInfoChannel` (Definition 13.6.1, the book's (23.15)) and `N^{⊗k}` the
published `WildeQIT.Degradable.tensorPower`. The input space is nonempty (on a zero-dimensional
input no code exists and `C_P = ⊥`). -/
theorem theorem_23_2_1 {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Nonempty a] (N : QChannel a b) :
    Filter.Tendsto
      (fun k : ℕ => ((WildeQIT.Degradable.privateInfoChannel
        (WildeQIT.Degradable.tensorPower N k) / k : ℝ) : EReal))
      Filter.atTop (nhds (privateCapacity N)) := by sorry

end WildeQIT.Compression.Supplement
