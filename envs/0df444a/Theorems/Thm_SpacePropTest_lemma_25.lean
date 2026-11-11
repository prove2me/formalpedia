-- Prove2me | Theorems.Thm_SpacePropTest_lemma_25
-- name    : SpacePropTest.lemma_25
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:56:37.095113+00:00
-- url     : https://prove2.me/theorems/5be4bd0a-6bec-42c2-90e1-bcda96be54a4
-- title:
--   Lemma 25, p.22 — a universal multiset of $n^{O(d)}/\eta^2$ edges approximates $\Pr_{i,x}[D_ih(x)\le t]$ for every degree-$d$ function $h$ and every $t$
-- statement:
--   There is an absolute constant $C$ such that for all $1\le d\le n$ and $\eta\in(0,1]$ there is a non-empty multiset $H_{d,\eta}$ of edges $(x,i)$, $x\in\{\pm1\}^n$, $i\in[n]$, with $|H_{d,\eta}|\le n^{Cd}/\eta^2$, such that for every $h:\{\pm1\}^n\to\mathbb R$ of Fourier degree at most $d$ and every $t\in\mathbb R$,
--
--   $$\Bigg|\frac1{|H_{d,\eta}|}\sum_{(x,i)\in H_{d,\eta}}\mathbf 1[D_ih(x)\le t]-\Pr_{i,x}[D_ih(x)\le t]\Bigg|\le\eta.$$
--
--   The set is fixed before $h$ and $t$, so a bounded-memory algorithm can iterate over hard-coded edges instead of storing query points.
--
--   Differences from the source:
--   - encoding: $f:\{\pm1\}^n\to\{\pm1\}$ on $\{\pm1\}^n$ → a Boolean function on $\{0,1\}^n$ (`Fin n → Bool`) read through $\mathrm{false}\mapsto-1$, $\mathrm{true}\mapsto+1$; reason: order-preserving bijection; the same monotone functions, derivatives and Fourier coefficients
--   - encoding: $\Pr_{x\sim\{\pm1\}^n,\,i\sim[n]}[\cdot]$ → the fraction of pairs $(x,i)\in\{0,1\}^n\times[n]$ satisfying the event; reason: $x$ and $i$ are uniform and independent
--   - encoding: $|H_{d,\eta}|=n^{O(d)}/\eta^2$; a (multi)set of edges → a non-empty list of pairs $(x,i)$ of length at most $n^{C\cdot d}/\eta^2$, $C$ absolute and chosen before $n,d,\eta$; reason: standard reading of $O(\cdot)$; the average $1/|H|$ needs $H$ non-empty
-- source:
--   Canonne, Chen, Pires, Pitassi, Servedio, The Space Complexity of Property Testing, manuscript of November 2, 2026 (sha256 65850aa6…), Lemma 25, p.22 (PDF 24)

import Mathlib
import Definitions.Def_SpacePropTest_Cube
import Definitions.Def_SpacePropTest_Fourier

set_option autoImplicit false

namespace SpacePropTest

/-- **Lemma 25** (C. Canonne, X. Chen, W. Pires, T. Pitassi, R. A. Servedio, *The Space Complexity
of Property Testing*, manuscript of November 2, 2026, sha256 65850aa6…; p.22 (PDF 24)). For
`1 ≤ d ≤ n` and `η ∈ (0, 1]` there is a multiset `H_{d,η}` of edges `(x, i)` with
`|H_{d,η}| = n^{O(d)}/η²` such that for every `h : {±1}ⁿ → ℝ` of Fourier degree at most `d` and
every `t ∈ ℝ`,
`|(1/|H|) ∑_{(x,i)∈H} 1[D_i h(x) ≤ t] − Pr_{i,x}[D_i h(x) ≤ t]| ≤ η`.

**Formalization Note.** The multiset is a non-empty list; `n^{O(d)}` is `n^{C·d}` with `C`
absolute, chosen before `n, d, η`. -/
theorem lemma_25 : ∃ C : ℕ, ∀ (n d : ℕ), 1 ≤ d → d ≤ n → ∀ (η : ℝ), 0 < η → η ≤ 1 →
    ∃ H : List (Cube n × Fin n), H ≠ [] ∧
      (H.length : ℝ) ≤ (n : ℝ) ^ (C * d) / η ^ 2 ∧
      ∀ h : Cube n → ℝ, DegreeLE d h → ∀ t : ℝ,
        |(H.countP (fun e => decide (deriv e.2 h e.1 ≤ t)) : ℝ) / H.length -
            edgeProbLe h t| ≤ η := by sorry

end SpacePropTest
