-- Prove2me | Theorems.Thm_QMAPlusGap_protocol_completeness_soundness
-- name    : QMAPlusGap.protocol_completeness_soundness
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T04:10:29.325454+00:00
-- url     : https://prove2.me/theorems/9daf8b9b-2e2e-414b-abb4-7de3de328e9c
-- title:
--   §4.2–4.3 — completeness $(1-e^{-\Omega(L)})^{2N}$ and soundness $1/4+\mathrm{poly}(\log M)M^{-\Omega_r(1)}$ of the protocol
-- statement:
--   Consider the two-proof protocol of §4.1 with exact symmetric-subspace measurements.
--
--   1. **Completeness.** For $0<\theta<c_0$ there is $\kappa_0>0$ such that for every proof space $\mathcal W=\mathbb C^\kappa$, acceptance operator $0\preceq A\preceq I$, unit vector $|h\rangle\ge0$ with $\langle h|A|h\rangle\ge c_0$, and all $L$ and $N\le M$: if $B$ is the threshold operator on $\mathcal H=\mathcal W^{\otimes L}$ and both Merlins send $(|h\rangle^{\otimes L})^{\otimes M}$, the protocol accepts with probability at least
--   $$
--   \big(1-e^{-\kappa_0L}\big)^{2N}.
--   $$
--   2. **Soundness.** For $r<1$ there are $C\ge0$, $k\in\mathbb N$, $\kappa>0$ and $M_0$ such that for every $\mathcal H=\mathbb C^\iota$, every $0\preceq B\preceq I$ with $\langle\psi|B|\psi\rangle\le r$ for all unit $|\psi\rangle\ge0$, every $M\ge M_0$ with $N=2\lfloor\tfrac14\log_2M\rfloor$, and all unit proofs $|\Psi_1\rangle,|\Psi_2\rangle\in\mathcal H^{\otimes M}$ with nonnegative amplitudes, the protocol accepts with probability at most
--   $$
--   \frac14+C(\log M)^kM^{-\kappa}.
--   $$
--
--   With $L=\lceil C'\log(n+2)\rceil$ and $M=(n+2)^C$ these give completeness $1-1/p(n)$ and soundness $1/4+1/p(n)$ in the main theorem (Lemma 8 supplies the hypotheses).
--
--   Differences from the source:
--   - generalization: the protocol's parameters L = ⌈C′ log(n + 2)⌉, M = (n + 2)^C, N = 2⌊(1/4) log₂ M⌋ in the completeness bound → completeness for every L and every N ≤ M; reason: the honest proof passes every symmetric test for any N ≤ M; the protocol's values are instances
--   - reading: c_new ≥ (1 − e^{−Ω(L)})^{2N}; soundness 1/4 + poly(log M) M^{−Ω_r(1)} after 'multiplying by the probability of reaching the conditional branch' → κ₀ > 0 depending only on (c0, θ); constants C, k, κ, M₀ depending only on r; an unconditional bound on the acceptance probability; reason: the Ω-constants come from Lemma 8 and Proposition 9; the paper concludes the unconditional bound
--   - encoding: the verifier's acceptance probability → protocolAccept with exact projectors P_sym^{(M)}, P_sym^{(2N)}; reason: §4.5 implements them to inverse-exponential accuracy, absorbed in the main theorem
--   - generalization: c0, θ and A of the one-proof verifier in §4.2; B the threshold operator of Lemma 8 in §4.3 → in completeness any 0 < θ < c0 and any 0 ⪯ A ⪯ I; in soundness any 0 ⪯ B ⪯ I on any finite ℂ^ι with ⟨ψ|B|ψ⟩ ≤ r < 1 for all unit ψ ≥ 0; reason: the bounds use only these properties; Lemma 8(ii) shows the threshold operator of a no instance has them with r = s0/θ, so the protocol is an instance
-- source:
--   Miyamoto, Near-Optimal Gap Amplification for Nonnegative Unentangled Quantum Proofs, arXiv:2608.07986 (held version, sha256 4667925f…), §4.2, p.16 and §4.3, pp.16–17 (protocol §4.1, p.16)

import Mathlib
import Definitions.Def_QMAPlusGap_IsNonnegVec
import Definitions.Def_ArgmaxDeFinetti_vnorm
import Definitions.Def_QMAPlusGap_expect
import Definitions.Def_QMAPlusGap_thresholdOp
import Definitions.Def_QMAPlusGap_protocolAccept

set_option autoImplicit false

open scoped MatrixOrder ComplexOrder
open MeasureTheory Filter

namespace QMAPlusGap

/-- **Completeness and soundness of the two-proof protocol**, Miyamoto, *Near-Optimal Gap Amplification for Nonnegative Unentangled Quantum Proofs*, arXiv:2608.07986 (held version, sha256 4667925f…), §4.2, p.16 and §4.3, pp.16–17.

Completeness (§4.2): "On a yes instance, let |h⟩ ≥ 0 be the honest proof for the one-proof verifier. Both Merlins
send (|h⟩^{⊗L})^{⊗M}. The two local symmetric-subspace measurements and the joint symmetric-subspace measurement
return their symmetric outcomes with probability one. Lemma 8(i) gives c_new ≥ (1 − e^{−Ω(L)})^{2N} = 1 − o(1)."

Soundness (§4.3): "Lemma 8(ii) supplies the condition needed for Proposition 9, which therefore bounds the
conditional probability that steps 3 and 4 both accept by 1/4 + poly(log M)M^{−Ω_r(1)}. Multiplying by the
probability of reaching the conditional branch can only decrease this expression."

Clause 1: for `0 < θ < c0` there is `κ₀ > 0` such that, for every proof space `W = ℂ^κ`, acceptance operator
`0 ⪯ A ⪯ I`, unit `h ≥ 0` with `⟨h|A|h⟩ ≥ c0` and all `L`, `N ≤ M`, the protocol with `B` the threshold operator
accepts `(h^{⊗L})^{⊗M}, (h^{⊗L})^{⊗M}` with probability `≥ (1 − e^{−κ₀L})^{2N}`. Clause 2: for `r < 1` there are
`C, k, κ > 0, M₀` such that for every `H = ℂ^ι`, `0 ⪯ B ⪯ I` with `⟨ψ|B|ψ⟩ ≤ r` for all unit `ψ ≥ 0`, every
`M ≥ M₀` with `N = 2⌊(1/4) log₂ M⌋`, and all unit nonnegative proofs `Ψ₁, Ψ₂`, the acceptance probability is
`≤ 1/4 + C (log M)^k M^{−κ}`.

**Formalization Note** The protocol's acceptance probability is `protocolAccept` (ideal, exact projectors). In
clause 1, `H = W^{⊗L}` has basis `Fin L → κ` and the honest proof has amplitude `∏_{i,l} h(z_{i,l})`; `= 1 − o(1)`
is commentary and not stated. Clause 1 is stated for every `N ≤ M`, which contains the protocol's
`N = 2⌊(1/4) log₂ M⌋`. -/
theorem protocol_completeness_soundness :
    (∀ c0 θ : ℝ, 0 < θ → θ < c0 → ∃ κ₀ : ℝ, 0 < κ₀ ∧
      ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (A : Matrix κ κ ℂ), A.PosSemidef → (1 - A).PosSemidef →
        ∀ h : κ → ℂ, IsNonnegVec h → ArgmaxDeFinetti.vnorm h = 1 → c0 ≤ (expect A h).re →
        ∀ L M N : ℕ, N ≤ M →
          (1 - Real.exp (-(κ₀ * L))) ^ (2 * N) ≤
            protocolAccept (thresholdOp A L θ) M N (fun z : Fin M → Fin L → κ => ∏ i, ∏ l, h (z i l))
              (fun z : Fin M → Fin L → κ => ∏ i, ∏ l, h (z i l))) ∧
    (∀ r : ℝ, r < 1 → ∃ (C : ℝ) (k : ℕ) (κ : ℝ) (M₀ : ℕ), 0 ≤ C ∧ 0 < κ ∧
      ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (B : Matrix ι ι ℂ), B.PosSemidef → (1 - B).PosSemidef →
        (∀ ψ : ι → ℂ, IsNonnegVec ψ → ArgmaxDeFinetti.vnorm ψ = 1 → (expect B ψ).re ≤ r) →
        ∀ M N : ℕ, M₀ ≤ M → N = 2 * ⌊(1 / 4 : ℝ) * Real.logb 2 M⌋₊ →
        ∀ Ψ₁ Ψ₂ : (Fin M → ι) → ℂ, IsNonnegVec Ψ₁ → ArgmaxDeFinetti.vnorm Ψ₁ = 1 → IsNonnegVec Ψ₂ → ArgmaxDeFinetti.vnorm Ψ₂ = 1 →
          protocolAccept B M N Ψ₁ Ψ₂ ≤ 1 / 4 + C * Real.log M ^ k * (M : ℝ) ^ (-κ)) := by sorry

end QMAPlusGap
