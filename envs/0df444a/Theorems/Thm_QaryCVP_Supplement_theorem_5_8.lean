-- Prove2me | Theorems.Thm_QaryCVP_Supplement_theorem_5_8
-- name    : QaryCVP.Supplement.theorem_5_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:16:07.92355+00:00
-- url     : https://prove2.me/theorems/a0bde0c7-05fd-49d5-b339-3dd57e75b5d3
-- title:
--   Theorem 5.8 — complexity of Algorithm 4: time exponent (41) and space exponent $\max\{\delta_0/4,\sup S_{in}(a)/(1-\kappa)\}$
-- statement:
--   Fix $D\ge1$ and rational constants $\delta_0\in(1/2,1)$, $\kappa\in(0,1)$, $\lambda,\varepsilon,\eta>0$, $c_0=1$, $c_1,\dots,c_k>0$, integers $k,\nu\ge1$. For $a>0$ let $T_{in}(a)$, $S_{in}(a)$ be the exponents (9) of the common enumeration at $t_i=c_i(p_a(1)+\lambda)$ and $\rho=(1-\kappa)H(p_a)$, and assume they are continuous (on a neighbourhood of $\{a>0:\delta_0\le H(p_a)\le D\}$). Suppose every completion uses dimension $n_0=\lceil n/(1-\kappa)\rceil$ and terminates in time $2^{(T_{in}(a)+o(1))n_0}$ and space $2^{(S_{in}(a)+o(1))n_0}$, uniformly over the input range, up to a polynomial in its input length: the enumeration is a program computing $R$, with these bounds on every call of the completion branch and every coin tape.
--
--   Then Algorithm 4 (a program implementing it, with an exact search, $\hat p$ and enclosures meeting their specifications) runs, on every input matrix with integers $q\ge2$, $n\ge1$, $m\ge0$ satisfying $\delta\le D$ and on every execution, in time $2^{Tn+o(n)}$ and space $2^{Sn+o(n)}$, up to factors polynomial in the binary input length, where
--
--   $$T=\max\Big\{\frac{\delta_0}2,\ \sup_{a>0:\ \delta_0\le H(p_a)\le D}\Big(H(r_a)+\varepsilon+\frac{T_{in}(a)}{1-\kappa}\Big)\Big\}\quad(41),\qquad S=\max\Big\{\frac{\delta_0}4,\ \sup_{a>0:\ \delta_0\le H(p_a)\le D}\frac{S_{in}(a)}{1-\kappa}\Big\}.$$
--
--   The terms account for the exact-search branch ($\delta_0/2$, $\delta_0/4$), the enumeration of prescribed coordinates ($H(r_a)+\varepsilon$) and one completion of dimension $n_0$ per case.
--
--   **Formalization Note** A program implements Algorithm 4 when there is a measurable assignment of the random choices to coin tapes under which its output on every tape is the output of the model `alg4` (with the given enumeration), and whose law under fair coins is within total-variation distance $2^{-n}$ of the model's law.
--
--   Differences from the source:
--   - reading: Algorithm 4 (a specific procedure) has the stated time and space → there is a program Pr whose output on every coin tape equals the model alg4's output at φ(τ), for a measurable assignment φ of its random choices whose law under fair coins is within total-variation distance 2^{-n} of the model's law (ImplementsAlg4), with the stated bounds; reason: base decisions 3 and 4; the equal-output clause ties the cost to Algorithm 4, so neither a trivial program nor a derandomized run on one unlucky assignment can satisfy it; the law is required only up to total-variation 2^{-n}, not exactly, because fair bits cannot sample Z/qZ exactly (Section E.6.4, error 2^{-Ω(n²)} per sample)
--   - reading: the exact search of Algorithm 2, b̂p computed as in E.6.1, the outward intervals of E.6.2 → existential: some nonzero exact search meeting Definition 3.4, some b̂p with 0 ≤ b̂p − p_a(1) ≤ min{n⁻², 10⁻¹²}, some enclosures of width ≤ 1, all used by Pr; reason: these subprocedures are internal to Algorithm 4; their stated specifications are what the theorem and its cost use
--   - reading: "where Tin, Sin are continuous" → continuous on an open set containing {a > 0 : δ0 ≤ H(p_a) ≤ D}; reason: the proof absorbs H(p_a) = δ + o(1), which may leave the range, by continuity (p.53: "a slightly enlarged compact range"); this is the weakest form the proof uses and continuity on a > 0 implies it
--   - reading: every completion terminates in time 2^{(Tin(a)+o(1))n0} and space 2^{(Sin(a)+o(1))n0}, uniformly over the input range → a program Rprog computing R on the completion calls (ComputesEnum) with RunsWithin bounds 2^{(Tin(a)+g(n0))n0}·(ℓ+1)^K and 2^{(Sin(a)+g(n0))n0}·(ℓ+1)^K on every call (inputs with n ≥ 2, m ≥ 1, q ≥ 3, q⁴ > n, δ0 < δ ≤ D) and every tape, one g → 0 and K for every accurate b̂p; reason: the completion is a subprocedure of the program; its proportions depend on b̂p, so the bound is required for each admissible one, uniformly
--   - encoding: sup over a > 0 with δ0 ≤ H(p_a) ≤ D → real sSup of the image of that set; reason: the set is compact and nonempty and the functions are continuous on it, so the supremum is finite and equals sSup
--   - encoding: δ = m log q / n ≤ D → the real density m log₂ q / n ≤ D (QaryCVP.density); reason: the same condition; D is a real constant
--   - reading: time and space in bit operations and bits, no machine named (p.13) → bit time and bit space of the published randomized log-cost rational RAM TwMSOCount.Main; reason: base decision 1 (R1); this machine charges bit operations at least as heavily
--   - reading: factors polynomial in the binary input length → (ℓ+1)^K with ℓ the total bit length of the input word and K fixed before the input; reason: p.13 (base R2)
--   - reading: o(n) in the exponent → one g : ℕ → ℝ with g(n)/n → 0, fixed before the input, shared by time and space; reason: p.13 asymptotic convention (base R3); one g is the stronger form
--   - reading: Input: H ∈ (Z/qZ)^{m×n} → the input word n, m, q, then the entries of H row by row as canonical representatives in [0, q) (encSVP); reason: base R9 without a target
--   - reading: on every input (every execution) → the run halts on every coin tape and the bounds hold on every tape; reason: p.13 and Theorem 5.9 "Every execution" (base R10)
-- source:
--   Kim, Kwon, Lee, Lee, Fast Provable Algorithms for Approximate CVP and Exact SVP on Random q-ary Lattices, STOC 2027 submission manuscript (sha256 9aeb2ff4…ab4), Theorem 5.8, p.54 (PDF 55); T_in(a), S_in(a), p.54; Algorithm 4, p.48; §5.1, pp.49–50

import Mathlib
import Definitions.Def_TwMSOCount_Main_Machine
import Definitions.Def_QaryCVP_qaryLattice
import Definitions.Def_QaryCVP_encInst
import Definitions.Def_QaryCVP_ent3
import Definitions.Def_QaryCVP_Supplement_svpBasics
import Definitions.Def_QaryCVP_Supplement_thetaDist
import Definitions.Def_QaryCVP_Supplement_svpExponents
import Definitions.Def_QaryCVP_Supplement_alg4

open MeasureTheory Filter Topology TwMSOCount.Main

namespace QaryCVP.Supplement

/-- **Theorem 5.8** (complexity of Algorithm 4). Kim, Kwon, Lee, Lee, STOC 2027 submission manuscript
(sha256 9aeb2ff4…ab4), Theorem 5.8, p.54; `T_in(a)`, `S_in(a)` defined on p.54; Algorithm 4, p.48.

Fix `D ≥ 1` and the constants `P` as in §5.1. Let `T_in(a)`, `S_in(a)` be the exponents (9) at
`tᵢ = cᵢ(p_a(1) + λ)`, `ρ = (1 − κ)H(p_a)`, and assume they are continuous (on a neighbourhood of the compact range
`{a > 0 : δ₀ ≤ H(p_a) ≤ D}`). Suppose every completion uses dimension `n₀ = ⌈n/(1 − κ)⌉` and
terminates in time `2^{(T_in(a)+o(1))n₀}` and space `2^{(S_in(a)+o(1))n₀}`, uniformly over the input
range: the enumeration is a program `Rprog` computing `R`, with these bounds (up to a polynomial in
its input length) on every call of the completion branch and every coin tape. Then there are an
accurate `b̂p`, valid enclosures, a nonzero exact search and a program `Pr` implementing Algorithm 4
with them and `R` such that, on every input matrix with `q ≥ 2`, `n ≥ 1`, `m ≥ 0`, `δ ≤ D`, every
execution takes time `2^{T n + o(n)}` and space `2^{S n + o(n)}`, up to a polynomial in the binary
input length, with
`T = max{δ₀/2, sup_{a>0: δ₀≤H(p_a)≤D} (H(r_a) + ε + T_in(a)/(1 − κ))}` (41) and
`S = max{δ₀/4, sup_{a>0: δ₀≤H(p_a)≤D} S_in(a)/(1 − κ)}`.

**Formalization Note.** Machine `TwMSOCount.Main` (R1); `o(n)` is one `g` with `g(n)/n → 0` (R3) and
the uniform `o(1)` of the completions one `g` with `g → 0`; polynomial factors are `(ℓ+1)^K` (R2).
"Algorithm 4" is a program whose output on every tape equals the model `alg4`'s at a measurable
assignment of its random choices whose law is within total variation `2^{−n}` of the model's
(`ImplementsAlg4`); its exact search, `b̂p` and enclosures are internal to it
and so are existential. "Where `T_in, S_in` are continuous" is read as continuity on an open
neighbourhood of the range of the suprema, the weakest form the proof uses (p.53: "a slightly
enlarged compact range containing the actual value `H(p_a) = δ + o(1)`"); continuity on `a > 0`
implies it. The completion hypothesis is required for every accurate `b̂p` (the
proportions passed to `R` depend on it), with one `g` uniform over them. -/
theorem theorem_5_8 (D : ℝ) (hD : 1 ≤ D) (P : Params) (hP : P.Admissible)
    (hcont : ∃ U : Set ℝ, IsOpen U ∧ aRange P.δ0 D ⊆ U ∧ ContinuousOn (TinA P) U ∧
      ContinuousOn (SinA P) U)
    (Rprog : Program) (R : EnumProc (ℕ → Bool)) (hR : ComputesEnum P D Rprog R)
    (hRcost : ∃ (g : ℕ → ℝ) (K : ℕ), Tendsto g atTop (𝓝 0) ∧
      ∀ bp : ℕ → ℕ → ℕ → ℚ, BpAccurate bp → ∀ n m q : ℕ, CompRange P D n m q →
        ∀ (A : Matrix (Fin m) (Fin (n0Of P.κ n)) (ZMod q)) (b : Fin m → ZMod q),
          RunsWithin Rprog (encComp P.k (propT P bp n m q) A b)
            ((2 : ℝ) ^ ((TinA P (aOf n m q) + g (n0Of P.κ n)) * (n0Of P.κ n : ℝ)) *
              polyF K (encComp P.k (propT P bp n m q) A b))
            ((2 : ℝ) ^ ((SinA P (aOf n m q) + g (n0Of P.κ n)) * (n0Of P.κ n : ℝ)) *
              polyF K (encComp P.k (propT P bp n m q) A b))) :
    ∃ (bp : ℕ → ℕ → ℕ → ℚ) (encl : Encl) (E0 : SearchProc),
      BpAccurate bp ∧ EnclValid P encl ∧ NonzeroSearchSpec E0 ∧
      ∃ (Pr : Program) (g : ℕ → ℝ) (K : ℕ), Tendsto (fun n => g n / n) atTop (𝓝 0) ∧
        ∀ n m q : ℕ, 1 ≤ n → 2 ≤ q → density q m n ≤ D →
          ∀ H : Matrix (Fin m) (Fin n) (ZMod q),
            RunsWithin Pr (encSVP H)
              ((2 : ℝ) ^ (svpTimeExp P D * n + g n) * polyF K (encSVP H))
              ((2 : ℝ) ^ (svpSpaceExp P D * n + g n) * polyF K (encSVP H)) ∧
            ImplementsAlg4 Pr P bp encl R E0 H := by sorry

end QaryCVP.Supplement
