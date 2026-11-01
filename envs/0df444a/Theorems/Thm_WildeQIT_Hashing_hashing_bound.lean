-- Prove2me | Theorems.Thm_WildeQIT_Hashing_hashing_bound
-- name    : WildeQIT.Hashing.hashing_bound
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:23:11.342044+00:00
-- url     : https://prove2.me/theorems/2f7633d1-0b7b-467e-a063-9cf0d1e0fdfa
-- title:
--   Theorem 24.6.2 (Hashing Bound): stabilizer codes achieve $1-H(p)$ on a Pauli channel
-- statement:
--   Let $p=(p_I,p_X,p_Y,p_Z)$ be a probability vector, $H(p)$ its entropy in bits, and $\mathcal N_p$ the Pauli channel
--
--   $$
--   \rho\mapsto p_I\rho+p_X\,X\rho X+p_Y\,Y\rho Y+p_Z\,Z\rho Z .
--   $$
--
--   Stabilizer codes achieve the **hashing bound** $R=1-H(p)$ for quantum communication over $\mathcal N_p$: for every $\varepsilon\in(0,1)$ and $\delta>0$ there is $N$ such that for every $n\ge N$ there exist
--
--   1. an integer $k$ with $k\ge n\,(1-H(p)-\delta)$,
--   2. an $[n,k]$ stabilizer code $\mathcal S$ (an abelian subgroup of the $n$-qubit Pauli group of size $2^{n-k}$ without $-I$),
--   3. an isometric encoding $V$ of $k$ qubits into the codespace of $\mathcal S$, and
--   4. a decoding channel $\mathcal D$ from $n$ qubits to $k$ qubits,
--
--   such that for every pure state $|\varphi\rangle_{RA_1}$ of $k$ logical qubits $A_1$ and a $k$-qubit reference $R$,
--
--   $$
--   \tfrac12\Bigl\|\varphi_{RA_1}-(\mathrm{id}_R\otimes\mathcal D\circ\mathcal N_p^{\otimes n}\circ\mathcal V)(\varphi_{RA_1})\Bigr\|_1\le\varepsilon,\qquad \mathcal V(\rho)=V\rho V^\dagger .
--   $$
--
--   That is, $1-H(p)$ is an achievable rate of quantum communication over $\mathcal N_p$ with codes that are stabilizer codes. The rate equals the coherent information of $\mathcal N_p$ evaluated on one share of a Bell state, so the theorem gives an explicit lower bound on the quantum capacity of every Pauli channel by codes with a group-theoretic description.
--
--   **Formalization Note** The Pauli channel's $n$-fold tensor power is the published `piSuperop`; the code criterion is (24.2) with the reference as first factor; entropy is `WildeQIT.entropy` (base 2). When $1-H(p)-\delta\le0$, $k=0$ meets the rate condition.
--
--   Differences from the source:
--   - reading: "there exists a stabilizer code that achieves the hashing bound $R=1-H(p)$" → for all $\varepsilon\in(0,1)$, $\delta>0$ and $n\ge N$ an $[n,k]$ stabilizer code with $k\ge n(1-H(p)-\delta)$, an encoder onto its codespace and a decoder forming an $(n,k/n,\varepsilon)$ code in the sense of (24.2); reason: the theorem's sentence has no quantifiers; §24.6.3 calls the bound "an achievable rate for quantum communication", which p. 659 defines this way, and the proof (24.106)–(24.120) establishes it
--   - encoding: an $(n,Q-\delta,\varepsilon)$ code, rate exactly $Q-\delta$ → rate $k/n\ge Q-\delta$; reason: $k$ is an integer, so the rate cannot equal $Q-\delta$ in general
--   - encoding: an abelian subgroup of size $2^{n-k}$ → also $-I\notin\mathcal S$; reason: implied by the book's $2^k$-dimensional codespace (p. 673); it excludes no $[n,k]$ code of the book
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, §24.6.3, Theorem 24.6.2, p. 674, eq. (24.104); proof pp. 674–676, (24.105)–(24.120); achievable rate §24.1, p. 659, (24.1)–(24.3)

import Definitions.Def_WildeQIT_Hashing_IsStabilizerCode
import Definitions.Def_WildeQIT_Hashing_IsStabilizerEncoder
import Definitions.Def_WildeQIT_Hashing_pauliChannelPow
import Definitions.Def_WildeQIT_Hashing_IsQCommCode
import Definitions.Def_WildeQIT_entropy

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, Theorem 24.6.2, p. 674.
-/

namespace WildeQIT.Hashing

open QAlgorithms Stabilizer

/-- **Theorem 24.6.2 (Hashing Bound)** (Wilde, *From Classical to Quantum Shannon Theory*,
arXiv:1106.1445v8, p. 674). Stabilizer codes achieve the rate `R = 1 − H(p)` over the Pauli
channel `ρ ↦ p_I ρ + p_X XρX + p_Y YρY + p_Z ZρZ` (24.104), `H(p)` the entropy of
`p = (p_I, p_X, p_Y, p_Z)`: for every `ε ∈ (0, 1)`, `δ > 0` and all sufficiently large `n` there
are `k ≥ n(1 − H(p) − δ)`, an `[n, k]` stabilizer code `S`, an isometric encoding `V` of `k`
qubits onto its codespace and a decoding channel `D` that form an `(n, k/n, ε)` quantum
communication code (24.2) for `N_p^{⊗n}`.

**Formalization Note.** "Achieves" is the book's notion of an achievable rate (p. 659: an
`(n, Q − δ, ε)` code for all `ε ∈ (0, 1)`, `δ > 0` and sufficiently large `n`), read with
rate at least `Q − δ`, the codes being stabilizer codes. Entropy is in bits
(`WildeQIT.entropy`). When `1 − H(p) − δ ≤ 0`, `k = 0` meets the rate condition. -/
theorem hashing_bound (p : WildeQIT.FinDist Pauli) :
    ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∀ n ≥ N, ∃ k : ℕ,
      (n : ℝ) * (1 - WildeQIT.entropy p - δ) ≤ k ∧
      ∃ S : Subgroup (Matrix.unitaryGroup (Qubits n) ℂ), IsStabilizerCode n k S ∧
      ∃ V : Matrix (Qubits n) (Qubits k) ℂ, IsStabilizerEncoder S V ∧
      ∃ D : Superop (Qubits n) (Qubits k),
        IsQCommCode (conjSuperop V) (pauliChannelPow p n) D ε := by sorry

end WildeQIT.Hashing
