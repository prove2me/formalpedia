-- Prove2me | Theorems.Thm_QuasilinearAG_Encoding_theorem_1_1
-- name    : QuasilinearAG.Encoding.theorem_1_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T15:42:21.256867+00:00
-- url     : https://prove2.me/theorems/72043861-a031-49e8-bfbb-b6285f9b1c4b
-- title:
--   Theorem 1.1 — codes over $\mathbb F_{q^2}$, $q<10/\varepsilon$, of every length $N$ and dimension $K\le(1-\varepsilon)N$, $d\ge N-K-\varepsilon N$, $N\mathrm{poly}(1/\varepsilon)\log^4N$ encoding
-- statement:
--   Let $0<\varepsilon<1$, and choose the least power of two $q\ge5/\varepsilon$, so $8\le q<10/\varepsilon$. For every integer $N\ge1$ and $0\le K\le(1-\varepsilon)N$ there is a deterministic $\mathbb F_{q^2}$-linear code of exact length $N$, dimension $K$ and distance $d\ge N-K-\varepsilon N$ (with $d=N$ for $K=0$). A coefficient-generator entry costs $\mathrm{poly}(\varepsilon^{-1},\log(N+2))$ bit operations. One can encode a coefficient vector ($E$) or construct the codeword with given values at the first $K$ ordered positions (systematic encoding); recover the coefficient vector from a codeword with the full-domain map $L=(S_KE)^{-1}S_K$; test membership; and apply the transposes $E^{\mathsf T}$, $L^{\mathsf T}$. Each of these operations is deterministic and takes
--   $$N\,\mathrm{poly}(\varepsilon^{-1})\,\log^4(N+2)$$
--   bit operations including setup, and uses $O(N\log(2+\varepsilon^{-1}))$ live bits in total, with an absolute constant in the space bound.
--
--   In Lean: there are absolute constants $c,C$, a representation $\mathbb F_{2^{2\sigma}}=\mathbb F_2[X]/(f_\sigma)$, a code family $G_{N,K,\sigma}$ ($N\times K$ coefficient generators) and seven coin-free programs of the log-cost RAM receiving the binary integers $N,K,\sigma$ (and $i,j$, or one record per field element) such that, for every $\varepsilon\in(0,1)$ with $\sigma=\sigma(\varepsilon)$, $8\le2^\sigma<10/\varepsilon$ and for all $N\ge1$, $K\le(1-\varepsilon)N$: $S_KG$ is invertible (dimension $K$, first $K$ positions an information set); every nonzero codeword has weight $\ge N-K-\varepsilon N$; the generator entry $G_{ij}$ is computed in $C(\varepsilon^{-1}\log_2(N+2))^c$ work; and $E$, the systematic encoder, $L$, membership, $E^{\mathsf T}$ and $L^{\mathsf T}$ each run within $C\varepsilon^{-c}N\log_2^4(N+2)$ work and $C\,N\log_2(2+\varepsilon^{-1})$ live bits at every step.
--
--   Differences from the source:
--   - encoding: F_{q²}, q = 2^σ, in a fixed polynomial basis → ∃ f : ℕ → F_2[X] with f σ irreducible of degree 2σ for every σ ≥ 1, field AdjoinRoot (f σ), elements as records n < 2^{2σ} (decodeField); reason: every such f gives an isomorphic field; §A3 uses the first irreducible polynomial in binary order, an instance; σ ≥ 1 because no polynomial of degree 0 is irreducible, and every σ used is σ(ε) ≥ 3
--   - encoding: packed random-access bit model; deterministic algorithms; bit operations; live bits → coin-free programs of the published log-cost RAM TimeSpaceMA_RAM; accumulated work; LiveBitsWithin at every reached state; inputs N, K, σ then records from cell 0, outputs as record lists (cell 0 = length); reason: the paper charges record bits plus address bits per access; complete storage includes inputs and outputs
--   - encoding: a code of length N and dimension K with distance d ≥ N − K − εN (d = N for K = 0) → a family G N K σ of N × K generators computed entrywise by Gen; S_K G invertible; every nonzero codeword has weight ≥ N − K − εN; reason: the minimum distance of a linear code is the least weight of a nonzero codeword; for K = 0 there is none, which is the convention d = N
--   - encoding: poly(·) and O(·) → absolute c, C quantified before ε, N, K and before the programs; reason: the paper states absolute constants (p. 7, p. 27)
-- source:
--   Chao, Liu, Li, Ma, Wang, Quasilinear Encoding at the Quadratic Alphabet Scale via Short Cartier Bases, STOC 2027 submission (manuscript sha256 355c15dc…), p. 2, Theorem 1.1 (PDF p. 4); proof completed p. 29 (PDF p. 31)

import Mathlib
import Definitions.Def_TimeSpaceMA_RAM
import Definitions.Def_QuasilinearAG_Encoding_Machine
import Definitions.Def_QuasilinearAG_Encoding_Code

namespace QuasilinearAG.Encoding

/-- Theorem 1.1 (Exact parameters and quadratic-alphabet encoding), p. 2 (PDF 4); proof completed
p. 29 (PDF 31). There are absolute constants `c, C`, a representation `F_{2^{2σ}} = F₂[X]/(f_σ)`
(`f_σ` irreducible of degree `2σ` for `σ ≥ 1`), a code family `G_{N,K,σ}` (`N × K` coefficient generators) and
seven coin-free programs of the log-cost RAM `TimeSpaceMA_RAM`, receiving the binary integers
`N, K, σ` (and `i, j`, or one record `< 2^{2σ}` per field element), such that for every
`0 < ε < 1`, with `q = 2^σ` the least power of two `≥ 5/ε` (so `8 ≤ q < 10/ε`), and all `N ≥ 1`,
`0 ≤ K ≤ (1 - ε)N`:
* the code `G F_{q²}^K` has exact length `N`, dimension `K` and its first `K` positions are an
  information set (`S_K G` is invertible), and every nonzero codeword has weight `≥ N - K - εN`;
* `Gen` computes the generator entry `G i j` from `(N, K, σ, i, j)` in `C(ε⁻¹ log₂(N + 2))^c` work;
* `Enc` (`m ↦ G m`), `Sys` (values on the first `K` positions `↦` the codeword), `Inv`
  (`w ↦ L w`, `L = (S_K E)⁻¹ S_K`, on every word), `Mem` (`w ∈ code`, answer `1`/`0`), `EncT`
  (`y ↦ Gᵀ y`) and `InvT` (`z ↦ Lᵀ z`) each take at most `C ε^{-c} N log₂⁴(N + 2)` work and
  `C N log₂(2 + ε⁻¹)` live bits at every step, setup included. -/
theorem theorem_1_1 :
    ∃ (c : ℕ) (C : ℝ), 0 < C ∧
    ∃ f : ℕ → Polynomial (ZMod 2), (∀ σ, 1 ≤ σ → Irreducible (f σ) ∧ (f σ).natDegree = 2 * σ) ∧
    ∃ G : (N K σ : ℕ) → Matrix (Fin N) (Fin K) (AdjoinRoot (f σ)),
    ∃ Gen Enc Sys Inv Mem EncT InvT : TimeSpaceMA.Program,
      Gen.CoinFree ∧ Enc.CoinFree ∧ Sys.CoinFree ∧ Inv.CoinFree ∧ Mem.CoinFree ∧
      EncT.CoinFree ∧ InvT.CoinFree ∧
      ∀ ε : ℝ, 0 < ε → ε < 1 →
        (8 : ℝ) ≤ 2 ^ sigmaOf ε ∧ (2 : ℝ) ^ sigmaOf ε < 10 / ε ∧
        ∀ N K : ℕ, 1 ≤ N → (K : ℝ) ≤ (1 - ε) * N →
          IsUnit (prefixRows (G N K (sigmaOf ε))) ∧
          (∀ w ∈ codeSpan (G N K (sigmaOf ε)), w ≠ 0 →
            (N : ℝ) - K - ε * N ≤ weight w) ∧
          (∀ (i : Fin N) (j : Fin K),
            Computes Gen [N, K, sigmaOf ε, i, j]
              (FieldVecOut (f (sigmaOf ε)) (sigmaOf ε) ![G N K (sigmaOf ε) i j])
              (C * (ε⁻¹ * Real.logb 2 (N + 2)) ^ c)) ∧
          (∀ r : Fin K → ℕ, (∀ j, r j < 2 ^ (2 * sigmaOf ε)) →
            ComputesInSpace Enc (inputLayout N K (sigmaOf ε) r)
              (FieldVecOut (f (sigmaOf ε)) (sigmaOf ε)
                ((G N K (sigmaOf ε)).mulVec (fun j => decodeField (f (sigmaOf ε)) (r j))))
              (C * ε⁻¹ ^ c * N * Real.logb 2 (N + 2) ^ 4) (C * N * Real.logb 2 (2 + ε⁻¹))) ∧
          (∀ r : Fin K → ℕ, (∀ j, r j < 2 ^ (2 * sigmaOf ε)) →
            ComputesInSpace Sys (inputLayout N K (sigmaOf ε) r)
              (FieldVecOut (f (sigmaOf ε)) (sigmaOf ε)
                (systematicEncode (G N K (sigmaOf ε))
                  (fun j => decodeField (f (sigmaOf ε)) (r j))))
              (C * ε⁻¹ ^ c * N * Real.logb 2 (N + 2) ^ 4) (C * N * Real.logb 2 (2 + ε⁻¹))) ∧
          (∀ r : Fin N → ℕ, (∀ i, r i < 2 ^ (2 * sigmaOf ε)) →
            ComputesInSpace Inv (inputLayout N K (sigmaOf ε) r)
              (FieldVecOut (f (sigmaOf ε)) (sigmaOf ε)
                ((recoverMat (G N K (sigmaOf ε))).mulVec
                  (fun i => decodeField (f (sigmaOf ε)) (r i))))
              (C * ε⁻¹ ^ c * N * Real.logb 2 (N + 2) ^ 4) (C * N * Real.logb 2 (2 + ε⁻¹))) ∧
          (∀ r : Fin N → ℕ, (∀ i, r i < 2 ^ (2 * sigmaOf ε)) →
            ComputesInSpace Mem (inputLayout N K (sigmaOf ε) r)
              (fun out =>
                (out = [1] ∧ (fun i => decodeField (f (sigmaOf ε)) (r i)) ∈
                    codeSpan (G N K (sigmaOf ε))) ∨
                (out = [0] ∧ (fun i => decodeField (f (sigmaOf ε)) (r i)) ∉
                    codeSpan (G N K (sigmaOf ε))))
              (C * ε⁻¹ ^ c * N * Real.logb 2 (N + 2) ^ 4) (C * N * Real.logb 2 (2 + ε⁻¹))) ∧
          (∀ r : Fin N → ℕ, (∀ i, r i < 2 ^ (2 * sigmaOf ε)) →
            ComputesInSpace EncT (inputLayout N K (sigmaOf ε) r)
              (FieldVecOut (f (sigmaOf ε)) (sigmaOf ε)
                ((G N K (sigmaOf ε)).transpose.mulVec
                  (fun i => decodeField (f (sigmaOf ε)) (r i))))
              (C * ε⁻¹ ^ c * N * Real.logb 2 (N + 2) ^ 4) (C * N * Real.logb 2 (2 + ε⁻¹))) ∧
          (∀ r : Fin K → ℕ, (∀ j, r j < 2 ^ (2 * sigmaOf ε)) →
            ComputesInSpace InvT (inputLayout N K (sigmaOf ε) r)
              (FieldVecOut (f (sigmaOf ε)) (sigmaOf ε)
                ((recoverMat (G N K (sigmaOf ε))).transpose.mulVec
                  (fun j => decodeField (f (sigmaOf ε)) (r j))))
              (C * ε⁻¹ ^ c * N * Real.logb 2 (N + 2) ^ 4) (C * N * Real.logb 2 (2 + ε⁻¹))) := by sorry

end QuasilinearAG.Encoding
