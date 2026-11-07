-- Prove2me | Theorems.Thm_SubmodSparsify_claim_4_3_time
-- name    : SubmodSparsify.claim_4_3_time
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:23:20.977434+00:00
-- url     : https://prove2.me/theorems/09268e3c-5eb9-424a-b97f-c23b7049cc3c
-- title:
--   Claim 4.3, second sentence — Algorithm 2 on a terminal family runs in time $O(mn^2T_{\min}(n)^2(T_{\mathrm{eval}}+n))$
-- statement:
--   Let $f_1, \dots, f_m : 2^{[n]} \to \mathbb R_{\ge 0}$ be submodular with $f_i(\emptyset) = f_i([n]) = 0$. When Algorithm 2 is applied to any of the $2n$ terminal families of Algorithm 1, namely $(f_i^{\to}(u, \cdot))_i$ or $(f_i^{\to}(\cdot, u))_i$ on $E = [n] \setminus \{u\}$, it runs in deterministic time
--
--   $$O\bigl(m n^2 T_{\min}(n)^2 (T_{\mathrm{eval}} + n)\bigr).$$
--
--   Precisely: there is an absolute constant $C$ such that for every time bound $T$ of submodular minimization there is one deterministic program on the $m$-oracle RAM which, on input $(n, m, u, \mathrm{dir})$ with $n, m \ge 1$ and oracles $f_1, \dots, f_m$ as above, halts with the shares $s_i^{(u)}$ (inside family, $\mathrm{dir} = 0$) or $t_i^{(u)}$ (outside family, $\mathrm{dir} = 1$) in its output cells, in time at most $C\, m\, n^2\, T(n)^2 (T_{\mathrm{eval}} + n)$ whenever each oracle query costs $T_{\mathrm{eval}} \ge 1$.
--
--   Each evaluation of $h_i(C) = f_i^{\to}(u, C)$ is itself a constrained submodular minimization, which explains the square of $T_{\min}$.
--
--   Differences from the source:
--   - encoding: ground set [n] = {1, …, n}, subsets of [n], components f_1, …, f_m → Fin n (paper index = value + 1), Finset (Fin n), f : Fin m → Finset (Fin n) → ℝ; reason: Lean representation; same instances
--   - encoding: standing assumption of §4 (p.18): every component normalized, f_i(∅) = f_i([n]) = 0, nonnegative submodular → explicit hypotheses hf0, hsub, hempty, huniv; reason: the section's standing hypotheses written as binders; same instances
--   - reading: running time O(·) in terms of Tmin(n), the time complexity of submodular minimization → ∃ C, ∀ T with SFMTime T (one FasterSFM program minimizes every submodular function on Fin n within T(n) steps), ∃ program with time ≤ C·(…)·T(n)²·(Teval + n); reason: Tmin(n) is any achievable SFM time bound; the constant C is absolute, chosen before T and the program (the stronger reading of O(·))
--   - encoding: "deterministic time", value-oracle queries costing Teval → a coin-free program of the m-oracle RAM SubmodSparsify.Machine; time = (work − queries) + Teval·queries, bounded for every real Teval ≥ 1; reason: the paper's cost model: queries at Teval, other operations at unit cost
--   - encoding: O(·) over instances → n ≥ 1 and m ≥ 1; reason: the bound concerns nonempty instances; at m = 0 the right-hand side is 0 while halting costs one step
--   - encoding: the algorithm outputs the weights → input [n, m] (or [n, m, u, dir]) in integer memory; the program halts with the i-th value in real-memory cell i; reason: a fixed input/output layout of the RAM; the f_i are reachable only through query
-- source:
--   Bao, Cai, Chen, He, Zhang, Nearly Optimal Submodular Sparsification, with and without Cardinality Constraints, arXiv:2606.20777 (version held, sha256 358242d6…), Claim 4.3, p.22 (PDF p.24); proof, p.23 (PDF p.25); p.3 (PDF p.5)

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_SubmodSparsify_weights
import Definitions.Def_SubmodSparsify_Machine
import Definitions.Def_SubmodSparsify_SFMTime

namespace SubmodSparsify

/-- **Claim 4.3, second sentence** (p.22): deterministic time of Algorithm 2 on a terminal
family.

Bao, Cai, Chen, He, Zhang, *Nearly Optimal Submodular Sparsification, with and without
Cardinality Constraints*, arXiv:2606.20777 (version held), Claim 4.3, p.22.

On any of the `2n` terminal families of Algorithm 1 (`(f→ᵢ(u, ·))ᵢ` or `(f→ᵢ(·, u))ᵢ` on
`E = [n] \ {u}`), Algorithm 2 runs in deterministic time `O(mn²Tmin(n)²(Teval + n))`: there is
an absolute `C` such that for every SFM time bound `T` there is one deterministic program that,
on input `(n, m, u, dir)` and oracles `f₁, …, f_m` satisfying the hypotheses of Theorem 4.1,
halts with the shares of the family (`dir = 0`: inside family, `s^{(u)}`; `dir = 1`: outside
family, `t^{(u)}`) in real-memory cells `0, …, m − 1`, in time at most
`C m n² T(n)² (Teval + n)` for every per-query cost `Teval ≥ 1`.

**Formalization Note.** `SFMTime T` says that one admissible program of the published value-oracle RAM
`FasterSFM.Machine` minimizes every submodular function on an `n`-element ground set within
`T n` steps (`Tmin(n) ≤ T(n)`). Algorithm 1 runs on the deterministic `m`-oracle RAM of module
`SubmodSparsify.Machine`; `charged s Teval` is its running time when each value query to an
`fᵢ` costs `Teval` and every other instruction costs `1`. The program is one finite list for all
`n`, `m`, `f`; the `fᵢ` are reachable only through `query`. `O(·)` is an absolute constant `C`,
chosen before the SFM time bound `T` and the program; `n, m ≥ 1` (the bound concerns nonempty
instances). The terminal families are those of normalized nonnegative
submodular `fᵢ` (p.24), so the hypotheses on `f` are those of Theorem 4.1 (standing assumption of
§4, p.18). The shares are those of (15) (module `SubmodSparsify.weights`). -/
theorem claim_4_3_time : ∃ C : ℝ, ∀ T : ℕ → ℕ, SFMTime T →
    ∃ P : Program, Admissible P ∧
      ∀ (n m : ℕ) (f : Fin m → Finset (Fin n) → ℝ) (hf0 : ∀ i S, 0 ≤ f i S)
        (hsub : ∀ i, NonmonotoneSubmod.Shared.Submodular (f i))
        (hempty : ∀ i, f i ∅ = 0) (huniv : ∀ i, f i Finset.univ = 0),
        1 ≤ n → 1 ≤ m → ∀ (u : Fin n) (dir : Bool), ∃ (t : ℕ) (s : State n),
          s = run P f [(n : ℤ), (m : ℤ), ((u : ℕ) : ℤ), if dir then 1 else 0] t ∧
          s.halted = true ∧
          (∀ i : Fin m, s.core.mem ((i : ℕ) : ℤ) =
            if dir then outShare f u i else inShare f u i) ∧
          ∀ Teval : ℝ, 1 ≤ Teval →
            charged s Teval ≤ C * m * n ^ 2 * ((T n : ℕ) : ℝ) ^ 2 * (Teval + n) := by sorry

end SubmodSparsify
