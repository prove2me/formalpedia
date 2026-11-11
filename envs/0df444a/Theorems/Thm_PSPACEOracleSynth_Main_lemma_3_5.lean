-- Prove2me | Theorems.Thm_PSPACEOracleSynth_Main_lemma_3_5
-- name    : PSPACEOracleSynth.Main.lemma_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:22:12.074316+00:00
-- url     : https://prove2.me/theorems/abfa2e2c-472f-4640-b445-dd67469aeecd
-- title:
--   Lemma 3.5 — $\mathcal E_N,\mathcal E'_N$ are $\kappa^{2N}$-near-isometries, the stage identity, and $G$-independent sparsity patterns
-- statement:
--   Let $G$ be a unitary on $H_d$, $d=k+s\le2^n$ (leading coordinates $1,\dots,k$, trailing coordinates $1,\dots,s$), with trailing block $\|G_{22}\|\le\kappa=3/4$, and let $N\ge1$. Then $\mathcal E_N$ and $\mathcal E'_N$ are $\kappa^{2N}$-near-isometries, and
--   $$\Bigl\|\Bigl(\bigoplus_z U^{(j+1)}(z)\Bigr)\mathcal E_N-\mathcal E'_NG\Bigr\|\le 8\kappa^N.$$
--   Each of $\Lambda_{\mathcal E}$, $\Lambda_{\mathcal E'}$ has a sparsity pattern of at most $N$ positions per row, which does not depend on $G$ and is computable from the row index in space polynomial in $n+N$.
--
--   Here $\beta=nN+\lceil\log_2(N+1)\rceil$, $Z(z)$, $U^{(j+1)}(z)=G_{11}+G_{12}Z(z)(I-G_{22}Z(z))^{-1}G_{21}$, $\mathcal E_N,\mathcal E'_N$ and $\Lambda_{\mathcal E},\Lambda_{\mathcal E'}$ are the objects of §3.3 (definition `Stage`), and $\|\cdot\|$ is the operator norm.
--
--   This lemma is one stage of the dimension recursion: it expresses $G$ through the smaller unitaries $U^{(j+1)}(z)$ up to error $8\kappa^N$, by maps whose Fourier coefficient matrices are row-sparse with a pattern known in advance, so that Lemma 3.6 can implement them.
--
--   **Formalization Note.** The two pattern families are chosen first, one pattern for each choice of the sizes $(n,N,k,s)$, and the statement then holds for every unitary $G$ satisfying the hypotheses. The space bound is for one oracle-free machine that receives the sizes and the row $(\zeta,c)$ (definition `PatternComputable`).
--
--   Differences from the source:
--   - reading: a split d = k + s of H_d, d ≤ 2^n (§3.3) → any k, s with k + s ≤ 2^n; reason: §3.3 states the lemma for a split of H_d, not for the specific s of Equation (3.2)
--   - encoding: control strings and frequencies in ℤ_{2^β}^{N+1}; E′_N(z) = E_N(−z) for G† → Fin (N+1) → Fin (2^β), exponents of ω in ℕ; E′_N(z) written with Z(z)† = Z(−z); reason: ω^{2^β} = 1, so the same matrices
--   - encoding: trailing coordinates λ = 1, …, s → r : Fin s with λ = r + 1 (frequency vector (1, λ, …, λ^N) with the 1-based λ); reason: relabelling; the frequency vectors are the paper's
--   - encoding: pattern computable from the row index in space polynomial in n + N → one oracle-free OTM, input tup [1^n, 1^N, bin k, bin s, ζ, c], at most p(n + N) cells, output the list of positions; reason: the sizes are part of the context in which the row index is given
-- source:
--   Sichen Wang, Unitary Synthesis with a PSPACE Oracle, STOC 2027 submission #1740 (October 2026), §3.3, Lemma 3.5, p. 20 (objects: Definition 3.2 and Equation (3.2), p. 16; Equations (3.4)–(3.7), p. 19; Λ_E, Λ_E′, p. 20)

import Mathlib
import Definitions.Def_PSPACEOracleSynth_Main_Dilation
import Definitions.Def_PSPACEOracleSynth_Main_ParamCircuit
import Definitions.Def_PSPACEOracleSynth_Main_Stage

open QAlgorithms.Complexity

namespace PSPACEOracleSynth.Main

/-- **Lemma 3.5**, Sichen Wang, *Unitary Synthesis with a PSPACE Oracle*, STOC 2027 submission
#1740, p. 20 (objects pp. 16, 19–20). Let `G` be a unitary on `H_d`, `d = k + s ≤ 2^n`, with
trailing block `‖G₂₂‖ ≤ κ = 3/4`, and let `N ≥ 1`. Then `E_N` and `E′_N` are
`κ^{2N}`-near-isometries, and `‖(⊕_z U^{(j+1)}(z)) E_N − E′_N G‖ ≤ 8κ^N`. Each of `Λ_E`, `Λ_E′`
has a sparsity pattern of at most `N` positions per row, which does not depend on `G` and is
computable from the row index in space polynomial in `n + N`.

The patterns are chosen before `G` (one pattern for each choice of the sizes `n, N, k, s`). -/
theorem lemma_3_5 :
    ∃ patE patE' : (n N k s : ℕ) → Ctrl n N × Fin k → Finset (Fin (k + s)),
      PatternComputable patE ∧ PatternComputable patE' ∧
      (∀ (n N k s : ℕ) (r : Ctrl n N × Fin k), 1 ≤ N →
        (patE n N k s r).card ≤ N ∧ (patE' n N k s r).card ≤ N) ∧
      ∀ (n N k s : ℕ) (G : Matrix (Fin (k + s)) (Fin (k + s)) ℂ),
        k + s ≤ 2 ^ n → 1 ≤ N → G ∈ Matrix.unitaryGroup (Fin (k + s)) ℂ →
        opNormR (blk22 G) ≤ kappa →
        IsNearIsometry (kappa ^ (2 * N)) (bigE n N k s G) ∧
        IsNearIsometry (kappa ^ (2 * N)) (bigE' n N k s G) ∧
        opNormR (sumNextU n N k s G * bigE n N k s G - bigE' n N k s G * G) ≤ 8 * kappa ^ N ∧
        IsSparsityPattern (lamE n N k s G) (patE n N k s) ∧
        IsSparsityPattern (lamE' n N k s G) (patE' n N k s) := by sorry

end PSPACEOracleSynth.Main
