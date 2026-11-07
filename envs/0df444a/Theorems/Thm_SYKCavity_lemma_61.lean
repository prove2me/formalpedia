-- Prove2me | Theorems.Thm_SYKCavity_lemma_61
-- name    : SYKCavity.lemma_61
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:35:49.848739+00:00
-- url     : https://prove2.me/theorems/a313eb4e-f28e-4367-996d-8f24e9cd439f
-- title:
--   Lemma 61 — the hierarchy (4.9) for the centered moments $\mu_p$ is exact
-- statement:
--   Let $\beta\ge0$, $N\ge1$, $p\ge1$, and write $G(a,b)=G_*(a,b)$ for the antisymmetric two-time saddle kernel. For all times $u,v,u_j,v_j\in[0,1]$ ($2\le j\le p$), with "rest" $=(u_j,v_j)_{j=2}^p$,
--   $$\mu_p\bigl((u,v),\text{rest}\bigr)-3\beta^2\int_0^1\!\!\int_0^1G(u,s)G(s,t)^2\mu_p\bigl((s,t),\text{rest}\bigr)G(t,v)\,ds\,dt=\operatorname{Alt}_{u,v}F(u,v),$$
--   where $\operatorname{Alt}_{u,v}F(u,v)=\tfrac12(F(u,v)-F(v,u))$ and
--   $$\begin{aligned}F(u,v)={}&\beta^2\int_0^1\!\!\int_0^1G(u,s)\Bigl[3G(s,t)G(t,v)\mu_{p+1}\bigl((s,t),(s,t),\text{rest}\bigr)+G(t,v)\mu_{p+2}\bigl((s,t)^{\times3},\text{rest}\bigr)\\&\quad+3G(s,t)^2\mu_{p+1}\bigl((s,t),(t,v),\text{rest}\bigr)+3G(s,t)\mu_{p+2}\bigl((s,t),(s,t),(t,v),\text{rest}\bigr)+\mu_{p+3}\bigl((s,t)^{\times3},(t,v),\text{rest}\bigr)\Bigr]ds\,dt\\&+\frac1N\sum_{j=2}^p\Bigl[\bigl(G(u,u_j)G(v_j,v)-G(u,v_j)G(u_j,v)\bigr)\mu_{p-2}(\text{rest}\setminus j)+G(u,u_j)\mu_{p-1}\bigl((v_j,v),\text{rest}\setminus j\bigr)-G(u,v_j)\mu_{p-1}\bigl((u_j,v),\text{rest}\setminus j\bigr)\Bigr].\end{aligned}$$
--   This is (4.9), with the coincident-time prescriptions of Lemma 42. Its order-one terms use only $\mu_{p+1},\mu_{p+2},\mu_{p+3}$ and its explicit $N^{-1}$ terms only $\mu_{p-1},\mu_{p-2}$.
--
--   Applying $\mathfrak L_\beta^{-1}$ (Lemma 5) to the first pair turns (4.9) into the recursion (4.12) that the algorithm solves.
--
--   **Formalization Note** $\mu_p$ is the value of $\langle\cdot\rangle_N$ (alternating prescription, applied to the whole centered expression; repeated pairs such as $(s,t),(s,t)$ are evaluated jointly inside the integral, as in (E.12)). "rest$\setminus j$" keeps the other pairs in increasing index order; for $p=1$ the $1/N$ sum is empty; $\mu_0=1$. The integrals are over $[0,1]^2$.
--
--   Differences from the source:
--   - encoding: the SYK Hamiltonian of Section 3, ψ_i Majoranas with {ψ_i, ψ_j} = 2δ_ij I → H = √(3/(8N³)) Σ_A J_A Γ_A with ψ_i the first N Jordan–Wigner generators on ⌈N/2⌉ qubits, sites Fin N; reason: standard representation (unique up to equivalence for even N); every milestone is a disorder average or uses Section 3's Γ-form as printed
--   - encoding: ⟨·⟩_N as the Grassmann ratio (3.19) → the trace-side expression (3.20) with Lemma 42's prescriptions (E.1)–(E.4), as the definition; reason: the page proves the two agree (3.20, Lemma 42); planning decision recorded for the moderator
--   - reading: "with the coincident-time evaluation prescriptions of Lemma 42" → μ's are the alternating values at every point of [0,1]^{2p}; the outer factors G*(a,b) take the value 0 at coinciding times; reason: Lemma 42 calls the alternating value the value of the Grassmann product; averaging the entire expression over orders factorizes across disjoint occurrences, so a coincident outer G* averages to 0; an ordered version is not determined by the page for the repeated integration pairs (E.12)
--   - encoding: μ_p((u,v),(u_j,v_j)_{j=2}^p) → p = q + 1, rest given by U, V : Fin q → ℝ; rest∖j by `skip`; ∫_0^1∫_0^1 ds dt as the integral over [0,1]²; reason: index bookkeeping
-- source:
--   Schmidhuber–Zlokapa, Polynomial-time algorithms for mean-field models up to the glass transition, arXiv:2610.06807 (held version, sha256 25d817ba…cfc5), Lemma 61, p.132; equation (4.9), pp.26–27; (4.10), p.27

import Mathlib
import Definitions.Def_SYKCavity_Correlator

open MeasureTheory

namespace SYKCavity

/-- **Lemma 61 (Exact equation for collective moments)**, p.132 of A. Schmidhuber, A. Zlokapa,
*Polynomial-time algorithms for mean-field models up to the glass transition*, arXiv:2610.06807
(held version, sha256 25d817ba…cfc5): equation (4.9), pp.26–27, is exact with the coincident-time
prescriptions of Lemma 42.

For `β ≥ 0`, `N ≥ 1`, `p = q + 1 ≥ 1` and all times `u, v, u_j, v_j ∈ [0, 1]` (`j = 2, …, p`, written
`U, V : Fin q → ℝ`), with `G(a, b) = G*(a, b)` the two-time kernel and `μ_p` the centered moments:
`μ_p((u,v), rest) − 3β² ∫∫ G(u,s) G(s,t)² μ_p((s,t), rest) G(t,v) ds dt = Alt_{u,v} F(u, v)`, where
`F(u, v) = β² ∫∫ G(u,s) [3G(s,t)G(t,v) μ_{p+1}((s,t),(s,t),rest) + G(t,v) μ_{p+2}((s,t)³,rest)
  + 3G(s,t)² μ_{p+1}((s,t),(t,v),rest) + 3G(s,t) μ_{p+2}((s,t),(s,t),(t,v),rest)
  + μ_{p+3}((s,t)³,(t,v),rest)] ds dt
  + (1/N) Σ_{j=2}^{p} [(G(u,u_j)G(v_j,v) − G(u,v_j)G(u_j,v)) μ_{p−2}(rest∖j)
  + G(u,u_j) μ_{p−1}((v_j,v), rest∖j) − G(u,v_j) μ_{p−1}((u_j,v), rest∖j)]`
and `Alt_{u,v} F(u, v) = (F(u, v) − F(v, u))/2` (4.10).

**Formalization Note.** `μ_p` is `muAlt` (the value of `⟨·⟩_N`, Lemma 42's alternating prescription,
applied to the entire centered expression; repeated pairs such as `(s,t),(s,t)` are evaluated jointly
inside the integral, as in (E.12)). `G(a, b) = gExt β (a − b)` (antisymmetric, antiperiodic,
`G(a, a) = 0`). `rest∖j` keeps the other pairs in increasing index order (`skip`); for `p = 1` the
`1/N` sum is empty. The double integrals are over `[0,1]²` (Lebesgue). The second sentence of
Lemma 61 (which moments occur) is visible in the shape of the equation. -/
theorem lemma_61 (β : ℝ) (hβ : 0 ≤ β) (N : ℕ) (hN : 1 ≤ N) (q : ℕ) (u v : ℝ)
    (U V : Fin q → ℝ) (hu : u ∈ Set.Icc (0 : ℝ) 1) (hv : v ∈ Set.Icc (0 : ℝ) 1)
    (hU : ∀ j, U j ∈ Set.Icc (0 : ℝ) 1) (hV : ∀ j, V j ∈ Set.Icc (0 : ℝ) 1) :
    let G : ℝ → ℝ → ℂ := fun a b => ((gExt β (a - b) : ℝ) : ℂ)
    let F : ℝ → ℝ → ℂ := fun a b =>
      ((β ^ 2 : ℝ) : ℂ) * ∫ x in Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1,
        G a x.1 *
          (3 * G x.1 x.2 * G x.2 b *
              muAlt β N (q + 2) (Fin.cons x.1 (Fin.cons x.1 U)) (Fin.cons x.2 (Fin.cons x.2 V)) +
            G x.2 b *
              muAlt β N (q + 3) (Fin.cons x.1 (Fin.cons x.1 (Fin.cons x.1 U)))
                (Fin.cons x.2 (Fin.cons x.2 (Fin.cons x.2 V))) +
            3 * G x.1 x.2 ^ 2 *
              muAlt β N (q + 2) (Fin.cons x.1 (Fin.cons x.2 U)) (Fin.cons x.2 (Fin.cons b V)) +
            3 * G x.1 x.2 *
              muAlt β N (q + 3) (Fin.cons x.1 (Fin.cons x.1 (Fin.cons x.2 U)))
                (Fin.cons x.2 (Fin.cons x.2 (Fin.cons b V))) +
            muAlt β N (q + 4) (Fin.cons x.1 (Fin.cons x.1 (Fin.cons x.1 (Fin.cons x.2 U))))
              (Fin.cons x.2 (Fin.cons x.2 (Fin.cons x.2 (Fin.cons b V))))) +
      ((N : ℂ))⁻¹ * ∑ j : Fin q,
        ((G a (U j) * G (V j) b - G a (V j) * G (U j) b) *
            muAlt β N (q - 1) (skip j U) (skip j V) +
          G a (U j) * muAlt β N (q - 1 + 1) (Fin.cons (V j) (skip j U)) (Fin.cons b (skip j V)) -
          G a (V j) * muAlt β N (q - 1 + 1) (Fin.cons (U j) (skip j U)) (Fin.cons b (skip j V)))
    muAlt β N (q + 1) (Fin.cons u U) (Fin.cons v V) -
        3 * ((β ^ 2 : ℝ) : ℂ) * ∫ x in Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1,
          G u x.1 * G x.1 x.2 ^ 2 * muAlt β N (q + 1) (Fin.cons x.1 U) (Fin.cons x.2 V) * G x.2 v =
      (F u v - F v u) / 2 := by sorry

end SYKCavity
