-- Prove2me | Theorems.Thm_QuantumStateIdentity321_Schur_theorem_1_3
-- name    : QuantumStateIdentity321.Schur.theorem_1_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T23:19:39.416934+00:00
-- url     : https://prove2.me/theorems/3b993029-d031-44da-a470-0f3d7d5a86cf
-- title:
--   Theorem 1.3 — relaxed quantum state identity with O(γ⁻² log(n/δ)) copies of each input state
-- statement:
--   For every $n\ge2$ input states of local dimension $d\ge2$, every overlap parameter $\varepsilon\in(0,1/4)$ and every $\delta\in(0,1)$, let $\gamma=\tfrac12-\sqrt\varepsilon$. There exists a quantum algorithm that solves QSI$^\varepsilon_n$ (Definition 1.1) with error probability at most $\delta$ using
--
--   $$O\!\left(\frac1{\gamma^2}\log\frac n\delta\right)$$
--
--   copies of each input state. That is, there is an absolute constant $C>0$ such that for all such $n,d,\varepsilon,\delta$ some tester using $m\le C\gamma^{-2}\log(n/\delta)$ copies of each input state, fixed independently of the unknown states, accepts every yes instance with probability at least $1-\delta$ (completeness error at most $\delta$) and rejects every no instance with probability at least $1-\delta$ (soundness error at most $\delta$).
--
--   Differences from the source:
--   - encoding: a quantum algorithm using copies of each input state → the accept effect $0\le A\le I$ of its overall two-outcome measurement on $\bigotimes_i|\psi_i\rangle^{\otimes m}$, with acceptance probability $\langle\Psi|A|\Psi\rangle$; reason: every algorithm (unitaries, ancillas, intermediate measurements, randomness) induces such an effect and every such effect is realized by a measurement, so the existence claim is unchanged
--   - encoding: $O(\gamma^{-2}\log(n/\delta))$ copies → an explicit absolute constant $C>0$, quantified before $n,d,\varepsilon,\delta$, bounding the number $m$ of copies of each state; reason: the big-O hides an absolute constant (the proof's $2L=2\lceil 8\gamma^{-2}\log(2n/\delta)\rceil$ is such a bound)
--   - encoding: indices $[n]=\{1,\dots,n\}$ → `Fin n`, and "rejects with probability at least $1-\delta$" → acceptance probability at most $\delta$; reason: Lean conventions, same instances
-- source:
--   Shih-Han Hung, Ming-Hsien Tsai, STOC 2027 submission #321 (October 2026), Theorem 1.3, PDF/printed pp.3–4, with Definition 1.1, p.2, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/321.pdf

import Definitions.Def_QuantumStateIdentity321_Schur_Model

namespace QuantumStateIdentity321.Schur

/-- Theorem 1.3, pp.3–4 (with Definition 1.1, p.2): there is an absolute constant `C` such that
for every number of inputs `n ≥ 2`, local dimension `d ≥ 2`, `ε ∈ (0, 1/4)` and `δ ∈ (0, 1)`,
with `γ = 1/2 − √ε`, some quantum tester using `m ≤ C · γ⁻² · log(n/δ)` copies of each input
state accepts every yes instance with probability at least `1 − δ` and accepts every no instance
with probability at most `δ` (rejects it with probability at least `1 − δ`). -/
theorem theorem_1_3 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (n d : ℕ), 2 ≤ n → 2 ≤ d →
      ∀ ε δ : ℝ, 0 < ε → ε < 1 / 4 → 0 < δ → δ < 1 →
        ∃ m : ℕ, (m : ℝ) ≤ C * (1 / (1 / 2 - Real.sqrt ε) ^ 2) * Real.log (n / δ) ∧
          ∃ T : Tester n m d,
            (∀ ψ : Fin n → State d, (∀ i, ‖ψ i‖ = 1) → IsYesInstance ε ψ →
                1 - δ ≤ acceptProb T ψ) ∧
            (∀ ψ : Fin n → State d, (∀ i, ‖ψ i‖ = 1) → IsNoInstance ε ψ →
                acceptProb T ψ ≤ δ) := by sorry

end QuantumStateIdentity321.Schur
