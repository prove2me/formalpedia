-- Prove2me | Theorems.Thm_QVolKLS_lemma_4_1
-- name    : QVolKLS.lemma_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:42:06.416899+00:00
-- url     : https://prove2.me/theorems/8f33e18f-1d3e-4835-baf2-9777942c1256
-- title:
--   Lemma 4.1 — quantum product estimator: $\sum_\ell\sigma_\ell(-\log\mathbb E_{\pi_\ell}[Y_\ell])$ to additive $\varepsilon$ with $\tilde O(n/\varepsilon)$ calls
-- statement:
--   There is an absolute constant $C>0$ with the following property. Let $n\ge1$, signs $\sigma_\ell\in\{-1,1\}$ and $0<\varepsilon<\tfrac12$. There is one quantum algorithm, making in total at most
--   $$
--   C\,\frac n\varepsilon\Big(1+\log\frac n\varepsilon\Big)^{C}
--   $$
--   calls to the controlled qsample reflections $R_{\pi_\ell}$ and to $V_{Y_\ell}$ and its inverse, such that: for all probability distributions $\pi_1,\dots,\pi_n$ on finite sets and random variables $Y_\ell$ with
--   $$
--   0\le Y_\ell\le1,\qquad \mathbb E_{\pi_\ell}[Y_\ell]\ge\tfrac1{32}\qquad(1\le\ell\le n),
--   $$
--   given one independent qsample $|\pi_\ell\rangle$ of each law, it outputs an estimate of
--   $$
--   \mathsf L=\sum_{\ell=1}^n\sigma_\ell\big(-\log\mathbb E_{\pi_\ell}[Y_\ell]\big)=-\log\prod_{\ell=1}^n\big(\mathbb E_{\pi_\ell}[Y_\ell]\big)^{\sigma_\ell}
--   $$
--   within additive error $\varepsilon$ with probability at least $49/50$. Moreover the qsamples may be supplied one at a time, each discarded before the next is needed, with the phase register shared between contributions.
--
--   Applied to the bridge probabilities of the cooling schedule, it estimates the logarithm of the telescoping product (51).
--
--   **Formalization Note** Each law lives on an $m$-qubit sample register (every finite set embeds). The algorithm is a circuit over arbitrary unitary gates with the $2n$ oracles $R_{\pi_\ell}\otimes I_Q$ and $V_{Y_\ell}$, chosen from $n,m,\sigma,\varepsilon$ before the laws; it must work for every unitary $V_\ell$ acting as $V_{Y_\ell}$ on $|x\rangle|0\rangle$. The output is the dyadic number on designated wires. "Supplied one at a time" is the streaming layout `IsStreamingSplit`.
--
--   Differences from the source:
--   - encoding: laws on finite sets → laws on the labels {0,1}^m of m-qubit sample registers; reason: every finite set embeds with zero weight on unused labels
--   - encoding: access to the controlled R_{π_ℓ} → an oracle R_{π_ℓ} ⊗ I_Q on m + 1 qubits, callable plainly, inversely or controlled; reason: the extra qubit is ignored, so the access is exactly that of R_{π_ℓ}
--   - reading: access to V_{Y_ℓ} (defined only on |x⟩|0⟩_Q) → every unitary V_ℓ with that action on |x⟩|0⟩; reason: the algorithm must work with any implementation of V_Y
--   - reading: Õ(n/ε) calls → C(n/ε)(1 + log(n/ε))^C calls with one absolute C; reason: Õ hides polylogarithmic factors in n/ε
--   - reading: there is a quantum algorithm → one circuit over arbitrary unitary gates chosen from n, m, σ, ε before the laws, measured at the end, with a dyadic output on designated wires; reason: the laws are accessed only through qsamples and oracles; the lemma counts calls only
--   - reading: the qsamples may be supplied one at a time, and each is discarded before the next is needed; the phase register is shared → IsStreamingSplit: prefix ++ B_1 ++ ⋯ ++ B_n ++ suffix, block B_ℓ touching only S_ℓ among sample registers and calling only oracles of contribution ℓ; reason: S_ℓ is untouched before B_ℓ and after it, so it can be supplied and discarded there
-- source:
--   R. Zhang, Improved Upper and Lower Bounds for Quantum Convex-Body Volume Estimation, arXiv:2610.04987 (preprint, held version, sha256 eee7a45e7117af08035a8d75fd6f145fa82ddade51ad87a6507911b6a0aa4f80), Lemma 4.1, p.30 (V_Y, p.30)

import Definitions.Def_QVolKLS_productOracles

set_option autoImplicit false

namespace QVolKLS

open QAlgorithms

/-- R. Zhang, arXiv:2610.04987 (held version, sha256 eee7a45e…), **Lemma 4.1 (Quantum product
estimator)**, p.30.

There is an absolute `C > 0` such that for every `n ≥ 1`, sample-register size `m`, signs
`σ_ℓ ∈ {−1, 1}` and `0 < ε < 1/2` there is one circuit with output wires, using in total at most
`C (n/ε)(1 + log(n/ε))^C` calls to the controlled reflections `R_{π_ℓ}` and to `V_{Y_ℓ}` and its
inverse, laid out in streaming form (`IsStreamingSplit`), such that: for all probability laws
`π_1, …, π_n` and random variables `0 ≤ Y_ℓ ≤ 1` with `E_{π_ℓ}[Y_ℓ] ≥ 1/32`, and every unitary
`V_ℓ` acting as `V_{Y_ℓ}` on `|x⟩|0⟩`, the circuit run on `|π_1⟩ ⊗ ⋯ ⊗ |π_n⟩ ⊗ |0⟩` outputs an
estimate within `ε` of
`L = Σ_ℓ σ_ℓ(−log E_{π_ℓ}[Y_ℓ]) = −log Π_ℓ (E_{π_ℓ}[Y_ℓ])^{σ_ℓ}` with probability at least `49/50`.

**Formalization Note.**
* Gates are arbitrary unitaries (`unitaryGateSet`; the lemma counts calls only). The `2n` oracles act
  on `m + 1` qubits: index `ℓ` is `R_{π_ℓ} ⊗ I_Q`, index `n + ℓ` is `V_ℓ` (`productOracles`); plain,
  inverse and controlled calls each count one. The circuit is chosen from `n`, `m`, `σ`, `ε` before
  the laws, which it sees only through the oracles and the input qsamples.
* Laws on arbitrary finite sets are placed on the labels `{0,1}^m` of the sample registers (zero weight
  on unused labels).
* `Õ(n/ε)` is read as `C (n/ε)(1 + log(n/ε))^C` with one absolute `C`.
* The output is the dyadic number `m · 2^e` on the output wires (`decodeDyadic`), read by measuring
  the final state in the computational basis.
* The streaming clause encodes "the qsamples may be supplied one at a time, and each is discarded
  before the next is needed; the phase register is shared": sample register `S_ℓ` is touched only by
  block `B_ℓ`, which calls only the oracles of contribution `ℓ`. -/
theorem lemma_4_1 :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ), 1 ≤ n → ∀ (m : ℕ) (σ : Fin n → ℤ), (∀ ℓ, σ ℓ = 1 ∨ σ ℓ = -1) →
      ∀ ε : ℝ, 0 < ε → ε < 1 / 2 →
        ∃ (w : ℕ) (c : OracleCircuit unitaryGateSet (fun _ : Fin (n + n) => m + 1) (n * m + w))
          (wo uo : ℕ) (mant : Fin wo ↪ Fin (n * m + w)) (expo : Fin uo ↪ Fin (n * m + w)),
          ((∑ k, c.queryCount k : ℕ) : ℝ) ≤
              C * ((n : ℝ) / ε) * (1 + Real.log ((n : ℝ) / ε)) ^ C ∧
          IsStreamingSplit c ∧
          ∀ (π Y : Fin n → Qubits m → ℝ)
            (V : Fin n → Matrix (Qubits (m + 1)) (Qubits (m + 1)) ℂ),
            (∀ ℓ x, 0 ≤ π ℓ x) → (∀ ℓ, ∑ x, π ℓ x = 1) →
            (∀ ℓ x, 0 ≤ Y ℓ x ∧ Y ℓ x ≤ 1) → (∀ ℓ, 1 / 32 ≤ ∑ x, π ℓ x * Y ℓ x) →
            (∀ ℓ, IsVYOracle (Y ℓ) (V ℓ)) →
            49 / 50 ≤ probWhere
              (opApply (c.unitary (productOracles π V)) (productInput w π))
              {z | |decodeDyadic mant expo z -
                  ∑ ℓ, (σ ℓ : ℝ) * (-Real.log (∑ x, π ℓ x * Y ℓ x))| ≤ ε} := by sorry

end QVolKLS
