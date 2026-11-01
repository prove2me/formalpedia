-- Prove2me | Theorems.Thm_WildeQIT_HSW_eq_20_64
-- name    : WildeQIT.HSW.eq_20_64
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T19:13:04.2338+00:00
-- url     : https://prove2.me/theorems/aba1a9bf-12e4-415b-bc8d-84edff81869e
-- title:
--   Eq. (20.64), converse bound: $\frac1n\log|\mathcal M|\,(1-\varepsilon) \le \frac1n\chi(\mathcal N^{\otimes n}) + \frac1n g_2(\varepsilon)$
-- statement:
--   Let $\mathcal N_{A'\to B}$ be a quantum channel, $n$ a number of channel uses, and $\mathcal M = \{1,\dots,|\mathcal M|\}$ a nonempty message set. Consider a randomness-distribution protocol: Alice encodes the uniformly distributed $m$ into a density operator $\rho^m_{A'^n}$, sends it through $\mathcal N^{\otimes n}$, and Bob measures a POVM $\{\Lambda_{m'}\}_{m'\in\mathcal M}$ on $B^n$. The resulting classical state and the ideal shared-randomness state are
--
--   $$
--   \omega_{MM'} = \sum_{m,m'}\frac1{|\mathcal M|}\mathrm{Tr}\{\Lambda_{m'}\mathcal N^{\otimes n}(\rho^m_{A'^n})\}\,|m\rangle\langle m|_M\otimes|m'\rangle\langle m'|_{M'},\qquad
--   \Phi_{MM'} = \sum_m\frac1{|\mathcal M|}|m\rangle\langle m|_M\otimes|m\rangle\langle m|_{M'} .
--   $$
--
--   If $\varepsilon\in[0,1]$ and $\tfrac12\|\Phi_{MM'}-\omega_{MM'}\|_1\le\varepsilon$, then
--
--   $$
--   \frac1n\log|\mathcal M|\,(1-\varepsilon) \ \le\ \frac1n\chi(\mathcal N^{\otimes n}) + \frac1n g_2(\varepsilon),
--   $$
--
--   where $\chi$ is the Holevo information of a channel and $g_2(\varepsilon) = (\varepsilon+1)\log_2(\varepsilon+1)-\varepsilon\log_2\varepsilon$.
--
--   A code for classical communication with maximal error at most $\varepsilon$ is such a protocol (its $\tfrac12\|\Phi-\omega\|_1$ is the average error probability), so this bound gives the converse part of the classical capacity theorem after $n\to\infty$.
--
--   **Formalization Note** Logarithms are base 2; $\Phi_{MM'}$ and $\omega_{MM'}$ are diagonal matrices on $\mathcal M\times\mathcal M$; $\|\cdot\|_1$ is the published `WildeQIT.traceNorm`; $\chi$ is the pure-state Holevo information (20.8). At $n=0$ both sides are $0$ under Lean's convention $1/0 = 0$.
--
--   Differences from the source:
--   - encoding: n ≥ 1 channel uses (the bound divides by n) → n : ℕ, so n = 0 is admitted; reason: at n = 0 Lean's 1/0 = 0 makes both sides 0, so the extra instance is the trivial 0 ≤ 0 and every instance with n ≥ 1 is the book's
--   - reading: error ε of a randomness-distribution protocol (20.21), range not restated in §20.2.2 → 0 ≤ ε ≤ 1; reason: ε ∈ [0, 1] is the range of the error of an (n, C, ε) code (p. 562) and the range in which the AFW inequality used for (20.63) holds; for ε > 1 the left side is ≤ 0 and the bound says nothing
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, §20.3.2, (20.56)–(20.64), pp. 570–571; §20.2.2, (20.16)–(20.21), p. 563

import Mathlib
import Definitions.Def_WildeQIT_QChannel
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_WildeQIT_traceNorm
import Definitions.Def_WildeQIT_QMemory_IsPOVM
import Definitions.Def_WildeQIT_HSW_tensorPowMap
import Definitions.Def_WildeQIT_HSW_holevoInfo
import Definitions.Def_WildeQIT_AFW_g2

namespace WildeQIT.HSW

/-- Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, §20.3.2, (20.64),
p. 571, for a randomness-distribution protocol of §20.2.2, pp. 563–564: Alice encodes the
uniformly distributed message `m ∈ M` into a state `ρ^m_{A′ⁿ}`, sends it through `N^⊗n`, and Bob
applies a POVM `{Λ_m}`; the resulting state is
`ω_{MM′} = Σ_{m,m′} (1/|M|) Tr{Λ_{m′} N^⊗n(ρ^m_{A′ⁿ})} |m⟩⟨m|_M ⊗ |m′⟩⟨m′|_{M′}` (20.20), and the
protocol has error `ε` when `½‖Φ_{MM′} − ω_{MM′}‖₁ ≤ ε` (20.21), with
`Φ_{MM′} = Σ_m (1/|M|) |m⟩⟨m|_M ⊗ |m⟩⟨m|_{M′}` (20.16). "Putting everything together, we find
that (1/n) log |M| (1 − ε) ≤ (1/n) χ(N^⊗n) + (1/n) g₂(ε). (20.64)"

**Formalization Note.** The message set is `Fin M` with `M ≥ 1`; `M × M′` is `Fin M × Fin M`,
and `Φ_{MM′}`, `ω_{MM′}` are the diagonal matrices of (20.16) and (20.20) in the standard basis.
`‖·‖₁` is the published `WildeQIT.traceNorm`, `N^⊗n` is `WildeQIT.HSW.tensorPowMap N n`, `χ` is
`WildeQIT.HSW.holevoInfo`, `g₂` is `WildeQIT.AFW.g2`, and `ε ∈ [0, 1]` as for an `(n, C, ε)` code
(p. 562). Logarithms are base 2. At `n = 0` both sides are `0` (Lean's `1/0 = 0`). -/
theorem eq_20_64 {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (N : WildeQIT.QChannel A B) (n M : ℕ) (hM : 0 < M)
    (ρ : Fin M → Matrix (Fin n → A) (Fin n → A) ℂ)
    (Λ : Fin M → Matrix (Fin n → B) (Fin n → B) ℂ)
    (hρ : ∀ m, WildeQIT.IsDensityOperator (ρ m)) (hΛ : WildeQIT.QMemory.IsPOVM Λ)
    (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (herr : WildeQIT.traceNorm
        (Matrix.diagonal (fun mm : Fin M × Fin M => if mm.1 = mm.2 then (M : ℂ)⁻¹ else 0) -
          Matrix.diagonal (fun mm : Fin M × Fin M =>
            (M : ℂ)⁻¹ * Matrix.trace (Λ mm.2 * tensorPowMap N n (ρ mm.1)))) / 2 ≤ ε) :
    (1 / (n : ℝ)) * Real.logb 2 M * (1 - ε) ≤
      (1 / (n : ℝ)) * holevoInfo (tensorPowMap N n) + (1 / (n : ℝ)) * WildeQIT.AFW.g2 ε := by sorry

end WildeQIT.HSW
