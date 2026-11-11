-- Prove2me | Theorems.Thm_QVolKLS_theorem_6_1
-- name    : QVolKLS.theorem_6_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:40:28.056024+00:00
-- url     : https://prove2.me/theorems/256dbd43-ac67-4d7a-a8cc-90d3addf37c3
-- title:
--   Theorem 6.1 — $\tilde O\big(d^{5/2}/\psi+d^{3/2}/(\psi\varepsilon)\big)$ coherent membership queries estimate $\mathrm{vol}(K)$ to relative error $\varepsilon$
-- statement:
--   Let $\psi_{D}$ denote the infimum of the Cheeger constant $\psi_{\mathrm{ch}}(\lambda)=\inf_{0<\lambda(A)<1}\lambda^+(A)/\min\{\lambda(A),1-\lambda(A)\}$ over all isotropic log-concave probability measures $\lambda$ on $\mathbb R^{D}$ (the reciprocal of the KLS constant).
--
--   There is an absolute constant $C>0$ with the following property. Let $d\ge1$, let $x_0\in\mathbb Q^d$, let $r,R,\psi,\varepsilon$ be rationals with
--   $$
--   0<r\le R,\qquad 0<\psi\le\psi_{d+1},\qquad 0<\varepsilon<\tfrac12,
--   $$
--   and put $\kappa=R/r$ and $\ell=$ the total bit length of $(x_0,r,R,\psi,\varepsilon)$. Then there is a quantum algorithm on finitely many qubits — one circuit over $\{H,T,\mathrm{CNOT}\}$ with calls to strong coherent membership oracles of the unknown body — such that:
--
--   1. it makes at most
--   $$
--   C\Big(\frac{d^{5/2}}{\psi}+\frac{d^{3/2}}{\psi\varepsilon}\Big)\log^{C}\!\Big(\frac{d\kappa}{\varepsilon\psi}\Big)
--   $$
--   membership queries on every execution;
--   2. it uses at most $C\big(d\kappa(1+\ell)/(\psi\varepsilon)\big)^{C}$ gates;
--   3. for every convex body $K\subset\mathbb R^d$ with $B(x_0,r)\subseteq K\subseteq B(x_0,R)$, its output $\hat V$ satisfies
--   $$
--   \Pr\big[(1-\varepsilon)\,\mathrm{vol}(K)\le\hat V\le(1+\varepsilon)\,\mathrm{vol}(K)\big]\ \ge\ \tfrac23 .
--   $$
--
--   The algorithm is fixed by the input data and sees $K$ only through the oracle. By the KLS bound $\psi_{d+1}^{-1}=O(1)$ (Song–Zhang; Bizeul–Klartag–Lehec, 2026), this gives $\tilde O(d^{5/2}+d^{3/2}/\varepsilon)$ queries, improving the previous quantum bound $\tilde O(d^3+d^{9/4}/\varepsilon)$ [CH23].
--
--   **Formalization Note** $\psi_{d+1}$ is `(SongZhangKLS.psiN (d+1))⁻¹` in $[0,\infty]$, the reciprocal of the published KLS constant. The algorithm is a `MemAlgorithm d`: its oracles are membership oracles at dyadic coordinate formats of its choosing, every plain, inverse or controlled call counts one query, the whole register is measured at the end, and $\hat V=m\cdot2^e$ is read from designated output wires.
--
--   Differences from the source:
--   - generalization: κ := R/r ≤ poly(d) → no bound on κ; the same absolute C for every κ ≥ 1; reason: App. C.5 (pp.87–89) uses κ only through Q = max{4, Dκ/(εψ)} and all bounds are polylogarithmic in Q; the statement specializes to the paper's for κ ≤ poly(d)
--   - reading: the remaining computation is polynomial in d, κ, ψ⁻¹, ε⁻¹ and the bit length of the input → the circuit's number of H, T, CNOT gates is at most C(dκ(1+ℓ)/(ψε))^C, the circuit being chosen from the input data before K; reason: the paper calls this the gate complexity (p.5) and compiles all classical computation into reversible circuits over a fixed gate set (App. C, p.79)
--   - reading: log^{O(1)}(dκ/(εψ)) → (log(dκ/(εψ)))^C with the same absolute C as the prefactor; reason: O(1) is an absolute exponent; dκ/(εψ) > 2 on every instance since ψ_{d+1} < 1
--   - encoding: membership answered at any finite precision chosen by the algorithm; a controlled query uses two ordinary calls → finitely many oracles memOracle K b p, one per two's-complement dyadic coordinate format (b, p); a controlled call counts one query; reason: the formats are the algorithm's chosen precisions; counting a controlled call once changes the count by a factor at most 2
--   - encoding: an algorithm with intermediate measurements and discards → one unitary circuit measured once at the end; reason: deferred-measurement principle; no query count changes
--   - encoding: outputs V̂ → V̂ = m·2^e read from designated output wires (two's-complement mantissa and exponent); reason: a fixed dyadic decoding keeps classical post-processing inside the gate count
--   - encoding: ψ_{d+1} = inf of ψ_ch over isotropic log-concave laws, λ⁺ via the open r-neighbourhood → (SongZhangKLS.psiN (d+1))⁻¹ in ℝ≥0∞, the reciprocal of sup_µ sup_A min{µ(A),1−µ(A)}/µ⁺(A) with µ⁺ via A + r·closedBall; reason: the reciprocal of the supremum of reciprocals is the infimum; the closed and open r-neighbourhoods give the same liminf
--   - reading: B(x₀, r) ⊆ K ⊆ B(x₀, R) with B(x, r) not specified open or closed → open inner ball, closed outer ball; reason: the stronger of the readings: an open inner ball and a closed outer ball admit the most bodies
-- source:
--   R. Zhang, Improved Upper and Lower Bounds for Quantum Convex-Body Volume Estimation, arXiv:2610.04987 (preprint, held version, sha256 eee7a45e7117af08035a8d75fd6f145fa82ddade51ad87a6507911b6a0aa4f80), Theorem 6.1, p.44 (= Theorem 1.1, p.5); KLS constant (2), p.5; §2.4, p.23

import Definitions.Def_QVolKLS_MemAlgorithm
import Definitions.Def_SongZhangKLS_cheegerPsi

set_option autoImplicit false

namespace QVolKLS

open MeasureTheory

/-- R. Zhang, *Improved Upper and Lower Bounds for Quantum Convex-Body Volume Estimation*,
arXiv:2610.04987 (held version, sha256 eee7a45e…), **Theorem 6.1 (Main theorem)**, p.44.

There is an absolute constant `C > 0` such that for every dimension `d ≥ 1`, rational point `x₀`,
rationals `0 < r ≤ R`, rational `0 < ψ ≤ ψ_{d+1}` and rational `0 < ε < 1/2` there is one algorithm
(a circuit over `{H, T, CNOT}` with membership-oracle calls, `MemAlgorithm d`) that makes at most
`C (d^{5/2}/ψ + d^{3/2}/(ψε)) log^C(dκ/(εψ))` membership queries (`κ = R/r`), has at most
`C (d κ (1 + ℓ)/(ψ ε))^C` gates (`ℓ` the input bit length), and, for every convex body `K` with
`B(x₀, r) ⊆ K ⊆ B(x₀, R)`, outputs `V̂ ∈ [(1 − ε) vol K, (1 + ε) vol K]` with probability at
least `2/3`.

**Formalization Note.**
* `ψ_{d+1}` is the paper's reciprocal KLS constant, the infimum of the Cheeger constant over isotropic
  log-concave laws on `ℝ^{d+1}` ((2), p.5). It is `(SongZhangKLS.psiN (d+1))⁻¹` in `ℝ≥0∞`, the
  reciprocal of the published KLS constant `ψ_n = sup_µ sup_A min{µ(A), 1 − µ(A)}/µ⁺(A)`
  (Minkowski enlargement by a closed ball; the paper's open `r`-neighbourhood gives the same
  `liminf`).
* The hypothesis `κ ≤ poly(d)` is dropped: the statement is claimed for every `κ ≥ 1` with the same
  absolute `C`.
* `log^{O(1)}` is `(log(dκ/(εψ)))^C` with the same absolute `C`; `dκ/(εψ) > 2` on every instance,
  since `ψ_{d+1} < 1`.
* "The remaining computation is polynomial" is the gate count over `{H, T, CNOT}`, bounded by
  `C (d κ (1 + ℓ)/(ψ ε))^C`. The circuit is chosen from the input data before `K`: one circuit serves
  every admissible `K`, which it sees only through the oracles. See `MemAlgorithm` for the oracle
  formats, query counting, the measurement at the end, and the dyadic output decoding.
* `B(x₀, r)` is the open ball and `B(x₀, R)` the closed ball; `vol K = (volume K).toReal`. -/
theorem theorem_6_1 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (d : ℕ), 1 ≤ d → ∀ (x0 : Fin d → ℚ) (r R ψ ε : ℚ),
        0 < r → r ≤ R → 0 < ψ →
        ENNReal.ofReal (ψ : ℝ) ≤ (SongZhangKLS.psiN (d + 1))⁻¹ →
        0 < ε → ε < 1 / 2 →
        ∃ A : MemAlgorithm d,
          (A.queries : ℝ) ≤
              C * ((d : ℝ) ^ (5 / 2 : ℝ) / (ψ : ℝ) + (d : ℝ) ^ (3 / 2 : ℝ) / ((ψ : ℝ) * (ε : ℝ))) *
                Real.log ((d : ℝ) * ((R : ℝ) / (r : ℝ)) / ((ε : ℝ) * (ψ : ℝ))) ^ C ∧
          (A.gates : ℝ) ≤
              C * ((d : ℝ) * ((R : ℝ) / (r : ℝ)) * (1 + (inputBitLen x0 r R ψ ε : ℝ)) /
                ((ψ : ℝ) * (ε : ℝ))) ^ C ∧
          ∀ K : Set (Euc d), IsConvexBody K →
            Metric.ball (ratPoint x0) (r : ℝ) ⊆ K → K ⊆ Metric.closedBall (ratPoint x0) (R : ℝ) →
            2 / 3 ≤ A.outProb K
              (Set.Icc ((1 - (ε : ℝ)) * (volume K).toReal) ((1 + (ε : ℝ)) * (volume K).toReal)) := by sorry

end QVolKLS
