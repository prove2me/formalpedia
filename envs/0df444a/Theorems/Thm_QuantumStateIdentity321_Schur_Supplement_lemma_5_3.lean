-- Prove2me | Theorems.Thm_QuantumStateIdentity321_Schur_Supplement_lemma_5_3
-- name    : QuantumStateIdentity321.Schur.Supplement.lemma_5_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:02:14.0362+00:00
-- url     : https://prove2.me/theorems/54d1be52-4a45-4292-adc2-16f924a9310a
-- title:
--   Lemma 5.3 — phase averaging turns $|\psi_\phi\rangle\langle\psi_\phi|^{\otimes m}$ into a binomial mixture of Dicke states
-- statement:
--   Let $p\in[0,1]$, $m\ge0$, and $|\psi_\phi\rangle=\sqrt{1-p}\,|0\rangle+e^{i\phi}\sqrt p\,|1\rangle$. Then
--
--   $$
--   \mathbb E_{\phi\sim\mathrm{Uniform}(0,2\pi)}\bigl[|\psi_\phi\rangle\langle\psi_\phi|^{\otimes m}\bigr]=\sum_{k=0}^m\binom mk p^k(1-p)^{m-k}\,|\mathrm{wt}_k\rangle\langle\mathrm{wt}_k| ,
--   $$
--
--   where $|\mathrm{wt}_k\rangle=\binom mk^{-1/2}\sum_{x\in\{0,1\}^m,\ |x|=k}|x\rangle$ is the uniform superposition of the $m$-bit strings of Hamming weight $k$.
--
--   So the phase-averaged state is diagonal in the Dicke basis with a $\mathrm{Binomial}(m,p)$ diagonal; this identifies distinguishing the averaged states of Problem 1 with Problem 2.
--
--   **Formalization Note** The expectation is the entrywise integral $\frac1{2\pi}\int_0^{2\pi}\psi_\phi^{\otimes m}(x)\,\overline{\psi_\phi^{\otimes m}(y)}\,d\phi$ on $2^m\times2^m$ matrices indexed by bit strings.
--
--   Differences from the source:
--   - encoding: E_{φ∼Uniform(0,2π)}[·] → the entrywise integral (1/2π) ∫₀^{2π} … dφ; reason: the expectation under the uniform law on [0, 2π)
-- source:
--   Shih-Han Hung, Ming-Hsien Tsai, STOC 2027 submission #321 (October 2026), Lemma 5.3, PDF/printed p.19, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/321.pdf

import Definitions.Def_QuantumStateIdentity321_Schur_Supplement_LowerBound

namespace QuantumStateIdentity321.Schur.Supplement

open Matrix

/-- Lemma 5.3, p.19: for `p ∈ [0, 1]` and `|ψ_φ⟩ = √(1 − p)|0⟩ + e^{iφ}√p|1⟩`,
`E_{φ ∼ Uniform(0, 2π)}[|ψ_φ⟩⟨ψ_φ|^{⊗m}] = Σ_{k=0}^m C(m,k) p^k (1 − p)^{m−k} |wt_k⟩⟨wt_k|`,
where `|wt_k⟩` is the uniform superposition of the `m`-bit strings of Hamming weight `k`. -/
theorem lemma_5_3 (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (m : ℕ) :
    phaseAveragedPower p m =
      ∑ k ∈ Finset.range (m + 1),
        ((m.choose k : ℝ) * p ^ k * (1 - p) ^ (m - k) : ℂ) •
          Matrix.vecMulVec (dicke m k) (star (dicke m k)) := by sorry

end QuantumStateIdentity321.Schur.Supplement
