-- Prove2me | Theorems.Thm_QAlgorithms_GottesmanThesis_erasureChannel_capacity
-- name    : QAlgorithms.GottesmanThesis.erasureChannel_capacity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-13T18:04:01.753915+00:00
-- url     : https://prove2.me/theorems/74504552-2901-4b63-ac2b-ccfd8c45933f
-- title:
--   The quantum capacity of the erasure channel is max(0, 1 − 2p)
-- statement:
--   Fix an erasure probability $p \in [0,1]$. The qubit erasure channel $\mathcal N_p$ acts independently on each qubit sent: with probability $1-p$ the qubit passes unchanged together with a classical flag $0$, and with probability $p$ it is replaced by the maximally mixed state $I/2$ together with the flag $1$, so that the receiver knows which qubits were erased. On $n$ qubits the channel is $\mathcal N_p^{\otimes n}$.
--
--   A rate $R \in \mathbb R$ is *achievable* (for quantum codes, equivalently one-way entanglement purification) if for every $\varepsilon > 0$ and $\delta > 0$ there is $N_0$ such that for every $n \ge N_0$ there are a number $k \ge (R-\delta)n$ of logical qubits, an encoding quantum channel $\mathcal E$ from $k$ qubits to $n$ qubits and a decoding quantum channel $\mathcal D$ from the channel output (qubits and erasure flags) to $k$ qubits with
--
--   $$
--   F_e\big(\mathcal D \circ \mathcal N_p^{\otimes n} \circ \mathcal E\big) \ge 1 - \varepsilon,
--   $$
--
--   where $F_e(\Phi) = \langle \Phi_k | (\mathrm{id} \otimes \Phi)(|\Phi_k\rangle\langle \Phi_k|) | \Phi_k \rangle$ is the entanglement fidelity with respect to the maximally entangled state $|\Phi_k\rangle$ of two $k$-qubit registers. The theorem states that the quantum capacity of the erasure channel is $\max(0, 1-2p)$, in the strong form that the set of achievable rates is exactly
--
--   $$
--   \{R : R \text{ achievable for } \mathcal N_p\} = \big(-\infty,\ \max(0, 1-2p)\big].
--   $$
--
--   In particular every rate below $1-2p$ is achievable (random stabilizer codes), no rate above $1-2p$ is (a no-cloning argument), and for $p \ge 1/2$ the capacity is zero.
--
--   **Formalization Note** The supremum of achievable rates is not written as a real `sSup` (which would be junk on an empty or unbounded set); instead the achievable set itself is characterized. Because the definition of achievability already has the slack $\delta$, the achievable set is closed, so the capacity $\max(0,1-2p)$ is itself an achievable rate. The author's errata note that the thesis's proof of the upper bound assumes there is no superadditivity when a noiseless channel is added to a zero-rate channel; the theorem itself is the established value (Bennett–DiVincenzo–Smolin).
-- source:
--   Daniel Gottesman, Stabilizer Codes and Quantum Error Correction, 1997 thesis, downloaded arXiv v1 PDF; PDF title page now prints 2024, PDF p. 90, §7.5. https://arxiv.org/pdf/quant-ph/9705052v1

import Definitions.Def_QAlgorithms_Defs_FTCircuit
set_option autoImplicit false

namespace QAlgorithms.GottesmanThesis

/-- Gottesman thesis §7.5, pp.90–91 (unnumbered): the quantum capacity of the qubit erasure
channel with erasure probability `p` is `max(0, 1 − 2p)`.

The erasure channel (frozen `erasureChannel n p`) acts independently on each of the `n` qubits:
with probability `1 − p` the qubit passes unchanged with flag `0`, with probability `p` it is
replaced by the maximally mixed state with flag `1`, so the receiver knows which qubits were
erased. A rate `R` is achievable (frozen `IsAchievableQRate`) when for all `ε, δ > 0` and all large
`n` there are an encoding channel of `k ≥ (R − δ) n` qubits into `n` qubits and a decoding channel
(seeing the flags) whose composite with the erasure channel has entanglement fidelity `≥ 1 − ε`
(the 1-EPP picture of §7.4; no classical feedback). The capacity being `max(0, 1 − 2p)` is stated
as: the achievable rates are exactly the `R ≤ max(0, 1 − 2p)` (the δ-slack in the definition makes
the set of achievable rates closed, so the supremum is attained).

Erratum (author's errata page): the thesis's proof of the upper bound `1 − 2p` assumes no
superadditivity when a noiseless channel is added to a zero-rate channel; the value itself is the
established one (Bennett–DiVincenzo–Smolin), and is stated unchanged. -/
theorem erasureChannel_capacity (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (R : ℝ) :
    IsAchievableQRate (fun n => erasureChannel n p) R ↔ R ≤ max 0 (1 - 2 * p) := by
  sorry

end QAlgorithms.GottesmanThesis
