-- Prove2me | Theorems.Thm_QuasilinearAG_Encoding_theorem_5_8
-- name    : QuasilinearAG.Encoding.theorem_5_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T15:42:12.808262+00:00
-- url     : https://prove2.me/theorems/ee3032d1-ee84-4746-9a18-842957a3201c
-- title:
--   Theorem 5.8 — exact $N$, $K\le(1-\varepsilon)N$ over $\mathbb F_{q^2}$, $q<10/\varepsilon$, $d\ge N-K-\varepsilon N$, $N\mathrm{poly}(\log(N+2),1/\varepsilon)$ encoding
-- statement:
--   Let $0<\varepsilon<1$ and let $q=2^\sigma$ be the least power of two with $q\ge5/\varepsilon$; hence $q<10/\varepsilon$. For every positive integer $N$ and every integer $0\le K\le(1-\varepsilon)N$ there is a deterministic $\mathbb F_{q^2}$-linear code with exact length $N$, dimension $K$ and $d\ge N-K-\varepsilon N$. For each fixed $\varepsilon$ the coefficient generator is strongly explicit; uniformly in $\varepsilon$, its entry work is $\mathrm{poly}(\log(N+2),1/\varepsilon)$. Encoding, systematic encoding, unencoding and membership testing take $N\,\mathrm{poly}(\log(N+2),1/\varepsilon)$ bit operations including setup, and so do the transposes of the linear encoding and inverse maps. All these algorithms use $O(N\log(1/\varepsilon+2))$ complete live bits. The alphabet is $O(\varepsilon^{-2})$.
--
--   In Lean: absolute $c,C$, a field representation $f$, a code family $G$ and seven coin-free programs (generator entry, $E$, systematic encoder, $L=(S_KE)^{-1}S_K$, membership, $E^{\mathsf T}$, $L^{\mathsf T}$) receiving $N,K,\sigma$, with the entry within $C(\varepsilon^{-1}\log_2(N+2))^c$ work, the six maps within $C\,N(\varepsilon^{-1}\log_2(N+2))^c$ work and $C\,N\log_2(\varepsilon^{-1}+2)$ live bits, $S_KG$ invertible, every nonzero codeword of weight $\ge N-K-\varepsilon N$, and $q<10/\varepsilon$, $q^2<100/\varepsilon^2$.
--
--   Differences from the source:
--   - encoding: F_{q²}, q = 2^σ, in a fixed polynomial basis → ∃ f : ℕ → F_2[X] with f σ irreducible of degree 2σ for every σ ≥ 1, field AdjoinRoot (f σ), elements as records n < 2^{2σ} (decodeField); reason: every such f gives an isomorphic field; §A3 uses the first irreducible polynomial in binary order, an instance; σ ≥ 1 because no polynomial of degree 0 is irreducible, and every σ used is σ(ε) ≥ 3
--   - encoding: packed random-access bit model; deterministic algorithms; bit operations; live bits → coin-free programs of the published log-cost RAM TimeSpaceMA_RAM; accumulated work; LiveBitsWithin at every reached state; inputs N, K, σ then records from cell 0, outputs as record lists (cell 0 = length); reason: the paper charges record bits plus address bits per access; complete storage includes inputs and outputs
--   - encoding: a code of length N and dimension K with distance d ≥ N − K − εN (d = N for K = 0) → a family G N K σ of N × K generators computed entrywise by Gen; S_K G invertible; every nonzero codeword has weight ≥ N − K − εN; reason: the minimum distance of a linear code is the least weight of a nonzero codeword; for K = 0 there is none, which is the convention d = N
--   - encoding: poly(·) and O(·) → absolute c, C quantified before ε, N, K and before the programs; reason: the paper states absolute constants (p. 7, p. 27)
--   - reading: "systematic encoding", "unencoding" and "the transposes of the … inverse maps" (positions unspecified in the statement) → the designated information set is the first K positions (S_K G invertible), and unencoding is the full-domain map L = (S_K E)^{-1} S_K; reason: the proof (p. 23) uses the first K ordered points of Lemma 5.6, and a transpose of the inverse map needs a linear map on all words; Theorem 1.1 states both explicitly
--   - reading: O(N log(1/ε + 2)) complete live bits; alphabet O(ε^{-2}) → C N log₂(ε^{-1} + 2) with the same absolute C; q² < 100/ε²; reason: the stronger reading; the proof gives an absolute constant and q < 10/ε
-- source:
--   Chao, Liu, Li, Ma, Wang, Quasilinear Encoding at the Quadratic Alphabet Scale via Short Cartier Bases, STOC 2027 submission (manuscript sha256 355c15dc…), p. 23, Theorem 5.8 (PDF p. 25)

import Mathlib
import Definitions.Def_TimeSpaceMA_RAM
import Definitions.Def_QuasilinearAG_Encoding_Machine
import Definitions.Def_QuasilinearAG_Encoding_Code

namespace QuasilinearAG.Encoding

/-- Theorem 5.8 (Exact length and dimension, uniform small alphabet), p. 23 (PDF 25). Let
`0 < ε < 1` and `q = 2^σ` the least power of two with `q ≥ 5/ε`; hence `q < 10/ε`. There are
absolute constants `c, C`, a representation `F_{2^{2σ}} = F₂[X]/(f_σ)` (`f_σ` irreducible of degree
`2σ` for `σ ≥ 1`), a code family `G_{N,K,σ}` and seven coin-free programs of the log-cost RAM, receiving
`N, K, σ` in binary, such that for every positive `N` and `0 ≤ K ≤ (1 - ε)N` the code over
`F_{q²}` has exact length `N`, dimension `K` (its first `K` positions are an information set) and
`d ≥ N - K - εN`; the coefficient generator is strongly explicit with entry work
`poly(log(N + 2), 1/ε)`; encoding, systematic encoding, unencoding (`L = (S_K E)⁻¹ S_K`),
membership testing and the transposes of the linear encoding and inverse maps take
`N poly(log(N + 2), 1/ε)` bit operations including setup, and `O(N log(1/ε + 2))` complete live
bits; the alphabet `q² < 100/ε²` is `O(ε⁻²)`. -/
theorem theorem_5_8 :
    ∃ (c : ℕ) (C : ℝ), 0 < C ∧
    ∃ f : ℕ → Polynomial (ZMod 2), (∀ σ, 1 ≤ σ → Irreducible (f σ) ∧ (f σ).natDegree = 2 * σ) ∧
    ∃ G : (N K σ : ℕ) → Matrix (Fin N) (Fin K) (AdjoinRoot (f σ)),
    ∃ Gen Enc Sys Inv Mem EncT InvT : TimeSpaceMA.Program,
      Gen.CoinFree ∧ Enc.CoinFree ∧ Sys.CoinFree ∧ Inv.CoinFree ∧ Mem.CoinFree ∧
      EncT.CoinFree ∧ InvT.CoinFree ∧
      ∀ ε : ℝ, 0 < ε → ε < 1 →
        (2 : ℝ) ^ sigmaOf ε < 10 / ε ∧ (2 : ℝ) ^ (2 * sigmaOf ε) < 100 / ε ^ 2 ∧
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
              (C * N * (ε⁻¹ * Real.logb 2 (N + 2)) ^ c) (C * N * Real.logb 2 (ε⁻¹ + 2))) ∧
          (∀ r : Fin K → ℕ, (∀ j, r j < 2 ^ (2 * sigmaOf ε)) →
            ComputesInSpace Sys (inputLayout N K (sigmaOf ε) r)
              (FieldVecOut (f (sigmaOf ε)) (sigmaOf ε)
                (systematicEncode (G N K (sigmaOf ε))
                  (fun j => decodeField (f (sigmaOf ε)) (r j))))
              (C * N * (ε⁻¹ * Real.logb 2 (N + 2)) ^ c) (C * N * Real.logb 2 (ε⁻¹ + 2))) ∧
          (∀ r : Fin N → ℕ, (∀ i, r i < 2 ^ (2 * sigmaOf ε)) →
            ComputesInSpace Inv (inputLayout N K (sigmaOf ε) r)
              (FieldVecOut (f (sigmaOf ε)) (sigmaOf ε)
                ((recoverMat (G N K (sigmaOf ε))).mulVec
                  (fun i => decodeField (f (sigmaOf ε)) (r i))))
              (C * N * (ε⁻¹ * Real.logb 2 (N + 2)) ^ c) (C * N * Real.logb 2 (ε⁻¹ + 2))) ∧
          (∀ r : Fin N → ℕ, (∀ i, r i < 2 ^ (2 * sigmaOf ε)) →
            ComputesInSpace Mem (inputLayout N K (sigmaOf ε) r)
              (fun out =>
                (out = [1] ∧ (fun i => decodeField (f (sigmaOf ε)) (r i)) ∈
                    codeSpan (G N K (sigmaOf ε))) ∨
                (out = [0] ∧ (fun i => decodeField (f (sigmaOf ε)) (r i)) ∉
                    codeSpan (G N K (sigmaOf ε))))
              (C * N * (ε⁻¹ * Real.logb 2 (N + 2)) ^ c) (C * N * Real.logb 2 (ε⁻¹ + 2))) ∧
          (∀ r : Fin N → ℕ, (∀ i, r i < 2 ^ (2 * sigmaOf ε)) →
            ComputesInSpace EncT (inputLayout N K (sigmaOf ε) r)
              (FieldVecOut (f (sigmaOf ε)) (sigmaOf ε)
                ((G N K (sigmaOf ε)).transpose.mulVec
                  (fun i => decodeField (f (sigmaOf ε)) (r i))))
              (C * N * (ε⁻¹ * Real.logb 2 (N + 2)) ^ c) (C * N * Real.logb 2 (ε⁻¹ + 2))) ∧
          (∀ r : Fin K → ℕ, (∀ j, r j < 2 ^ (2 * sigmaOf ε)) →
            ComputesInSpace InvT (inputLayout N K (sigmaOf ε) r)
              (FieldVecOut (f (sigmaOf ε)) (sigmaOf ε)
                ((recoverMat (G N K (sigmaOf ε))).transpose.mulVec
                  (fun j => decodeField (f (sigmaOf ε)) (r j))))
              (C * N * (ε⁻¹ * Real.logb 2 (N + 2)) ^ c) (C * N * Real.logb 2 (ε⁻¹ + 2))) := by sorry

end QuasilinearAG.Encoding
